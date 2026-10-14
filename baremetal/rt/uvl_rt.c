/*
 * uvl_rt.c: the bare-metal Lean runtime for UVL.
 *
 * The C that Lean generates only needs a few dozen runtime entry points from
 * <lean/lean.h>; everything else is inline. This file provides them on top of
 * a single static memory pool, replacing libleanrt (C++, threads, GMP,
 * mimalloc, libuv) with ~1000 lines of freestanding C99:
 *
 *   - heap:      a static pool with size-class free lists and boundary-free
 *                coalescing on demand; no malloc, no system heap;
 *   - objects:   reference-count release, persistence, closures (apply),
 *                arrays, byte arrays, strings, thunks;
 *   - numbers:   "small bignums": Nat/Int beyond the boxed range are held in
 *                64 bits (Nat < 2^64, |Int| < 2^63); anything larger panics;
 *   - once:      lazily initialized closed terms (single-threaded).
 *
 * Lean's own reference counting frees every temporary as soon as it dies, so
 * the pool's high-water mark is the peak live set (one tile's worth of work
 * plus the UI state), not the total allocated over a frame.
 */
#include <lean/lean.h>
#include <string.h>
#include <math.h>
#include "uvl.h"

/* ------------------------------------------------------------------------ */
/* Panics                                                                    */

__attribute__((weak)) void uvl_on_panic(const char *msg, int fatal) {
    (void)msg;
    if (fatal) for (;;) { }
}

static LEAN_NORETURN void fatal(const char *msg) {
    uvl_on_panic(msg, 1);
    for (;;) { }
}

void lean_internal_panic(char const *msg) { fatal(msg); }
void lean_internal_panic_out_of_memory(void) { fatal("uvl: out of memory (increase UVL_HEAP_SIZE)"); }
void lean_internal_panic_unreachable(void) { fatal("uvl: unreachable code"); }
void lean_internal_panic_rc_overflow(void) { fatal("uvl: reference count overflow"); }
void lean_internal_panic_overflow(void) { fatal("uvl: integer overflow"); }
void lean_set_exit_on_panic(bool flag) { (void)flag; }
void lean_set_panic_messages(bool flag) { (void)flag; }
void lean_panic(char const *msg, bool force_stderr) { (void)force_stderr; uvl_on_panic(msg, 0); }
void lean_notify_assert(const char *file, int line, const char *cond) {
    (void)file; (void)line; (void)cond;
    fatal("uvl: assertion failed");
}

lean_object *lean_panic_fn(lean_object *default_val, lean_object *msg) {
    uvl_on_panic(lean_string_cstr(msg), 0);
    lean_dec(msg);
    return default_val;
}

lean_object *lean_panic_fn_borrowed(b_lean_obj_arg default_val, lean_object *msg) {
    lean_inc(default_val);
    return lean_panic_fn(default_val, msg);
}

void lean_inc_heartbeat(void) { }
void lean_initialize(void) { }
void lean_initialize_runtime_module(void) { }

/* ------------------------------------------------------------------------ */
/* Heap: static pool                                                         */

#ifndef UVL_HEAP_SIZE
#define UVL_HEAP_SIZE (96 * 1024)
#endif

#define ALIGN 8u
#define NCLASS 64u                       /* exact size classes 8, 16, …, 512 */
#define FREE_BIT (~(SIZE_MAX >> 1))      /* marks a free block's header word */

/* Every block starts with a size_t word. Allocated blocks: lean.h stores the
   requested object size there (non-mimalloc layout). Free blocks: block size
   with FREE_BIT, followed by the free-list link. Hence the heap can be walked
   linearly, which is all coalescing needs. */
typedef struct free_block {
    size_t header;
    struct free_block *next;
} free_block;

static uint8_t heap[UVL_HEAP_SIZE] __attribute__((aligned(8)));
static size_t heap_top;                  /* bump pointer */
static free_block *classes[NCLASS + 1];  /* classes[i]: blocks of exactly 8*i bytes */
static free_block *big;                  /* blocks > 512 bytes, unsorted */
static size_t live_bytes, peak_live, peak_top, n_allocs, n_coalesce;

static inline size_t round_up(size_t n) { return (n + ALIGN - 1) & ~(size_t)(ALIGN - 1); }
static inline size_t min_block(void) { return round_up(sizeof(free_block)); }

static void push_free(uint8_t *p, size_t size) {
    free_block *b = (free_block *)p;
    b->header = size | FREE_BIT;
    if (size / ALIGN <= NCLASS) {
        b->next = classes[size / ALIGN];
        classes[size / ALIGN] = b;
    } else {
        b->next = big;
        big = b;
    }
}

/* Merge adjacent free blocks and give the tail back to the bump region. */
static void coalesce(void) {
    n_coalesce++;
    memset(classes, 0, sizeof classes);
    big = NULL;
    size_t i = 0, run_start = 0, run = 0;
    while (i < heap_top) {
        size_t h = *(size_t *)(heap + i);
        size_t size = (h & FREE_BIT) ? (h & ~FREE_BIT) : round_up(h);
        if (h & FREE_BIT) {
            if (run == 0) run_start = i;
            run += size;
        } else if (run) {
            push_free(heap + run_start, run);
            run = 0;
        }
        i += size;
    }
    if (run) heap_top = run_start;  /* trailing free space returns to the bump region */
}

static void *take_big(size_t size) {
    free_block **best = NULL;
    for (free_block **pp = &big; *pp; pp = &(*pp)->next) {
        size_t s = (*pp)->header & ~FREE_BIT;
        if (s >= size && (!best || s < (((*best)->header) & ~FREE_BIT))) {
            best = pp;
            if (s == size) break;
        }
    }
    if (!best) return NULL;
    free_block *b = *best;
    *best = b->next;
    size_t s = b->header & ~FREE_BIT;
    if (s - size >= min_block()) push_free((uint8_t *)b + size, s - size);
    else size = s; /* cannot happen with 8-byte classes, kept for safety */
    return b;
}

static void *alloc_block(size_t size) {
    if (size / ALIGN <= NCLASS && classes[size / ALIGN]) {
        free_block *b = classes[size / ALIGN];
        classes[size / ALIGN] = b->next;
        return b;
    }
    void *p = take_big(size);
    if (p) return p;
    /* split a larger small block before growing */
    for (size_t c = size / ALIGN + 1; c <= NCLASS && size / ALIGN <= NCLASS; c++) {
        if (classes[c] && c * ALIGN - size >= min_block()) {
            free_block *b = classes[c];
            classes[c] = b->next;
            push_free((uint8_t *)b + size, c * ALIGN - size);
            return b;
        }
    }
    if (heap_top + size <= UVL_HEAP_SIZE) {
        p = heap + heap_top;
        heap_top += size;
        if (heap_top > peak_top) peak_top = heap_top;
        return p;
    }
    return NULL;
}

/* `malloc` as seen by lean.h (see include/lean/config.h). `n` already counts
   the size_t header that lean.h writes at the start of the block. */
#ifdef UVL_TRACE_ALLOC
#include <stdio.h>
#endif

void *uvl_heap_alloc(size_t n) {
    size_t size = round_up(n < sizeof(free_block) ? sizeof(free_block) : n);
#ifdef UVL_TRACE_ALLOC
    if (size >= UVL_TRACE_ALLOC) fprintf(stderr, "uvl alloc %zu (live %zu)\n", size, live_bytes);
#endif
    void *p = alloc_block(size);
    if (!p) {
        coalesce();
        p = alloc_block(size);
        if (!p) lean_internal_panic_out_of_memory();
    }
    live_bytes += size;
    if (live_bytes > peak_live) peak_live = live_bytes;
    n_allocs++;
    return p;
}

/* `free_sized` as seen by lean.h. */
void uvl_heap_free(void *p, size_t n) {
    size_t size = round_up(n < sizeof(free_block) ? sizeof(free_block) : n);
    live_bytes -= size;
    push_free((uint8_t *)p, size);
}

void uvl_heap_free_unsized(void *p) {
    uvl_heap_free(p, *(size_t *)p + sizeof(size_t));
}

void uvl_heap_stats(uvl_heap_info *out) {
    out->capacity = UVL_HEAP_SIZE;
    out->live = live_bytes;
    out->peak_live = peak_live;
    out->peak_top = peak_top;
    out->allocations = n_allocs;
    out->coalesces = n_coalesce;
}

lean_object *lean_alloc_object(size_t sz) {
    size_t *mem = (size_t *)uvl_heap_alloc(sizeof(size_t) + sz);
    *mem = sz;
    return (lean_object *)(mem + 1);
}

void lean_free_object(lean_object *o) {
    size_t *mem = (size_t *)o - 1;
    uvl_heap_free(mem, *mem + sizeof(size_t));
}

size_t lean_object_byte_size(lean_object *o) { return *((size_t *)o - 1); }
size_t lean_object_data_byte_size(lean_object *o) { return lean_object_byte_size(o); }

/* ------------------------------------------------------------------------ */
/* Object graph: release and persistence                                     */

typedef void (*child_fn)(lean_object *child, void *ctx);

static inline void each_child(lean_object *o, child_fn f, void *ctx) {
    switch (lean_ptr_tag(o)) {
    case LeanClosure: {
        unsigned n = lean_closure_num_fixed(o);
        for (unsigned i = 0; i < n; i++) f(lean_closure_arg_cptr(o)[i], ctx);
        break;
    }
    case LeanArray: {
        size_t n = lean_array_size(o);
        for (size_t i = 0; i < n; i++) f(lean_array_cptr(o)[i], ctx);
        break;
    }
    case LeanScalarArray: case LeanString: case LeanMPZ: case LeanExternal:
        break;
    case LeanThunk: {
        lean_thunk_object *t = lean_to_thunk(o);
        if (t->m_value) f(t->m_value, ctx);
        if (t->m_closure) f(t->m_closure, ctx);
        break;
    }
    case LeanRef:
        if (lean_to_ref(o)->m_value) f(lean_to_ref(o)->m_value, ctx);
        break;
    case LeanTask: case LeanPromise:
        fatal("uvl: tasks are not supported on bare metal");
    default: {
        unsigned n = lean_ctor_num_objs(o);
        for (unsigned i = 0; i < n; i++) f(lean_ctor_get(o, i), ctx);
    }
    }
}

/* Deletion uses a small explicit stack so long lists do not recurse deeply
   (MCU stacks are a few KB); on overflow it falls back to recursion. */
#define DEL_STACK 64
typedef struct { lean_object *items[DEL_STACK]; unsigned n; } del_stack;

static void del_object(lean_object *o);

static void release_child(lean_object *c, void *ctx) {
    if (lean_is_scalar(c)) return;
    int rc = lean_internal_get_rc(c);
    if (rc > 1) { c->m_rc = rc - 1; return; }
    if (rc != 1) return;  /* persistent */
    del_stack *s = (del_stack *)ctx;
    if (s->n < DEL_STACK) s->items[s->n++] = c;
    else del_object(c);
}

static void del_object(lean_object *o) {
    del_stack s;
    s.n = 0;
    s.items[s.n++] = o;
    while (s.n) {
        lean_object *x = s.items[--s.n];
        if (lean_ptr_tag(x) == LeanExternal) {
            lean_external_object *e = lean_to_external(x);
            e->m_class->m_finalize(e->m_data);
        } else {
            each_child(x, release_child, &s);
        }
        lean_free_object(x);
    }
}

void lean_dec_ref_cold(lean_object *o) {
    if (lean_internal_get_rc(o) == 1) del_object(o);
    /* multi-threaded / sticky counts never occur: no tasks on bare metal */
}

void lean_inc_ref_huge_n(lean_object *o, size_t n) {
    if (lean_is_st(o)) o->m_rc = (int)((unsigned)o->m_rc + (unsigned)n);
}

static void persist_child(lean_object *c, void *ctx) {
    (void)ctx;
    if (!lean_is_scalar(c) && lean_internal_get_rc(c) != 0) lean_mark_persistent(c);
}

void lean_mark_persistent(lean_object *o) {
    if (lean_is_scalar(o) || lean_internal_get_rc(o) == 0) return;
    o->m_rc = 0;
    each_child(o, persist_child, NULL);
}

void lean_mark_mt(lean_object *o) { (void)o; }

/* ------------------------------------------------------------------------ */
/* Once cells (closed terms are initialized on first use)                    */

#define ONCE(T, NAME)                                                         \
    T NAME(T *loc, lean_once_cell_t *tok, T (*init)(void)) {                 \
        if (tok->state != 1) { *loc = init(); tok->state = 1; }              \
        return *loc;                                                          \
    }
lean_object *lean_obj_once_cold(lean_object **loc, lean_once_cell_t *tok, lean_object *(*init)(void)) {
    if (tok->state != 1) {
        lean_object *v = init();
        lean_mark_persistent(v);
        *loc = v;
        tok->state = 1;
    }
    return *loc;
}
ONCE(uint8_t, lean_uint8_once_cold)
ONCE(uint16_t, lean_uint16_once_cold)
ONCE(uint32_t, lean_uint32_once_cold)
ONCE(uint64_t, lean_uint64_once_cold)
ONCE(size_t, lean_usize_once_cold)
ONCE(float, lean_float32_once_cold)
ONCE(double, lean_float_once_cold)

/* ------------------------------------------------------------------------ */
/* Closures                                                                  */

typedef lean_object *obj;
typedef obj (*f1)(obj); typedef obj (*f2)(obj, obj); typedef obj (*f3)(obj, obj, obj);
typedef obj (*f4)(obj, obj, obj, obj); typedef obj (*f5)(obj, obj, obj, obj, obj);
typedef obj (*f6)(obj, obj, obj, obj, obj, obj);
typedef obj (*f7)(obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f8)(obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f9)(obj, obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f10)(obj, obj, obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f11)(obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f12)(obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f13)(obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f14)(obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f15)(obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*f16)(obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj, obj);
typedef obj (*fn_args)(obj *);

static obj call_fun(void *fun, unsigned n, obj *a) {
    switch (n) {
    case 1: return ((f1)fun)(a[0]);
    case 2: return ((f2)fun)(a[0], a[1]);
    case 3: return ((f3)fun)(a[0], a[1], a[2]);
    case 4: return ((f4)fun)(a[0], a[1], a[2], a[3]);
    case 5: return ((f5)fun)(a[0], a[1], a[2], a[3], a[4]);
    case 6: return ((f6)fun)(a[0], a[1], a[2], a[3], a[4], a[5]);
    case 7: return ((f7)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6]);
    case 8: return ((f8)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
    case 9: return ((f9)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8]);
    case 10: return ((f10)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9]);
    case 11: return ((f11)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10]);
    case 12: return ((f12)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11]);
    case 13: return ((f13)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12]);
    case 14: return ((f14)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13]);
    case 15: return ((f15)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14]);
    case 16: return ((f16)fun)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14], a[15]);
    default: return ((fn_args)fun)(a);  /* arity > 16: arguments passed as an array */
    }
}

/* Move (unique closure) or copy (shared closure) the fixed arguments of `f`
   into `dst`, then release `f`'s shell. */
static void take_fixed(obj f, obj *dst) {
    unsigned k = lean_closure_num_fixed(f);
    obj *src = lean_closure_arg_cptr(f);
    if (lean_is_exclusive(f)) {
        for (unsigned i = 0; i < k; i++) dst[i] = src[i];
        lean_free_object(f);
    } else {
        for (unsigned i = 0; i < k; i++) { lean_inc(src[i]); dst[i] = src[i]; }
        lean_dec(f);
    }
}

obj lean_apply_n(obj f, unsigned n, obj *args) {
    unsigned arity = lean_closure_arity(f);
    unsigned fixed = lean_closure_num_fixed(f);
    void *fun = lean_closure_fun(f);
    if (fixed + n < arity) {
        obj r = lean_alloc_closure(fun, arity, fixed + n);
        take_fixed(f, lean_closure_arg_cptr(r));
        for (unsigned i = 0; i < n; i++) lean_closure_arg_cptr(r)[fixed + i] = args[i];
        return r;
    }
    obj all[arity];
    take_fixed(f, all);
    unsigned used = arity - fixed;
    for (unsigned i = 0; i < used; i++) all[fixed + i] = args[i];
    obj r = call_fun(fun, arity, all);
    if (used == n) return r;
    return lean_apply_n(r, n - used, args + used);
}

obj lean_apply_m(obj f, unsigned n, obj *args) { return lean_apply_n(f, n, args); }
obj lean_apply_1(obj f, obj a1) { obj a[] = {a1}; return lean_apply_n(f, 1, a); }
obj lean_apply_2(obj f, obj a1, obj a2) { obj a[] = {a1, a2}; return lean_apply_n(f, 2, a); }
obj lean_apply_3(obj f, obj a1, obj a2, obj a3) { obj a[] = {a1, a2, a3}; return lean_apply_n(f, 3, a); }
obj lean_apply_4(obj f, obj a1, obj a2, obj a3, obj a4) { obj a[] = {a1, a2, a3, a4}; return lean_apply_n(f, 4, a); }
obj lean_apply_5(obj f, obj a1, obj a2, obj a3, obj a4, obj a5) {
    obj a[] = {a1, a2, a3, a4, a5}; return lean_apply_n(f, 5, a);
}
obj lean_apply_6(obj f, obj a1, obj a2, obj a3, obj a4, obj a5, obj a6) {
    obj a[] = {a1, a2, a3, a4, a5, a6}; return lean_apply_n(f, 6, a);
}
obj lean_apply_7(obj f, obj a1, obj a2, obj a3, obj a4, obj a5, obj a6, obj a7) {
    obj a[] = {a1, a2, a3, a4, a5, a6, a7}; return lean_apply_n(f, 7, a);
}
obj lean_apply_8(obj f, obj a1, obj a2, obj a3, obj a4, obj a5, obj a6, obj a7, obj a8) {
    obj a[] = {a1, a2, a3, a4, a5, a6, a7, a8}; return lean_apply_n(f, 8, a);
}
obj lean_apply_9(obj f, obj a1, obj a2, obj a3, obj a4, obj a5, obj a6, obj a7, obj a8, obj a9) {
    obj a[] = {a1, a2, a3, a4, a5, a6, a7, a8, a9}; return lean_apply_n(f, 9, a);
}
obj lean_apply_10(obj f, obj a1, obj a2, obj a3, obj a4, obj a5, obj a6, obj a7, obj a8, obj a9, obj a10) {
    obj a[] = {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10}; return lean_apply_n(f, 10, a);
}

/* ------------------------------------------------------------------------ */
/* Thunks                                                                    */

obj lean_thunk_get_core(obj t) {
    lean_thunk_object *th = lean_to_thunk(t);
    obj c = th->m_closure;
    th->m_closure = NULL;
    obj v = lean_apply_1(c, lean_box(0));
    th->m_value = v;
    return v;
}

/* ------------------------------------------------------------------------ */
/* Arrays                                                                    */

obj lean_array_get_panic(obj def_val) {
    uvl_on_panic("index out of bounds", 0);
    return def_val;
}

obj lean_array_set_panic(obj a, obj v) {
    uvl_on_panic("index out of bounds", 0);
    lean_dec(v);
    return a;
}

obj lean_copy_expand_array(obj a, bool expand) {
    size_t sz = lean_array_size(a);
    size_t cap = lean_array_capacity(a);
    if (expand) cap = (cap + 1) * 2;
    obj r = lean_alloc_array(sz, cap);
    obj *src = lean_array_cptr(a), *dst = lean_array_cptr(r);
    if (lean_is_exclusive(a)) {
        memcpy(dst, src, sz * sizeof(obj));
        lean_free_object(a);
    } else {
        for (size_t i = 0; i < sz; i++) { lean_inc(src[i]); dst[i] = src[i]; }
        lean_dec(a);
    }
    return r;
}

obj lean_copy_expand_array_nonlinear(obj a, bool expand) { return lean_copy_expand_array(a, expand); }

obj lean_array_push(obj a, obj v) {
    obj r = a;
    if (!lean_is_exclusive(a) || lean_array_size(a) == lean_array_capacity(a))
        r = lean_copy_expand_array(a, lean_array_size(a) == lean_array_capacity(a));
    lean_array_object *o = (lean_array_object *)r;
    o->m_data[o->m_size++] = v;
    return r;
}

obj lean_mk_array(obj n, obj v) {
    if (!lean_is_scalar(n)) lean_internal_panic_out_of_memory();
    size_t sz = lean_unbox(n);
    obj r = lean_alloc_array(sz, sz);
    obj *d = lean_array_cptr(r);
    for (size_t i = 0; i < sz; i++) d[i] = v;
    if (sz == 0) lean_dec(v);
    else if (sz > 1) lean_inc_n(v, sz - 1);
    return r;
}

obj lean_array_mk(obj lst) {
    size_t n = 0;
    for (obj l = lst; !lean_is_scalar(l); l = lean_ctor_get(l, 1)) n++;
    obj r = lean_alloc_array(n, n);
    obj *d = lean_array_cptr(r);
    size_t i = 0;
    for (obj l = lst; !lean_is_scalar(l); l = lean_ctor_get(l, 1)) {
        obj x = lean_ctor_get(l, 0);
        lean_inc(x);
        d[i++] = x;
    }
    lean_dec(lst);
    return r;
}

obj lean_array_to_list(obj a) {
    size_t n = lean_array_size(a);
    obj r = lean_box(0);
    for (size_t i = n; i-- > 0;) {
        obj x = lean_array_get_core(a, i);
        lean_inc(x);
        obj c = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(c, 0, x);
        lean_ctor_set(c, 1, r);
        r = c;
    }
    lean_dec(a);
    return r;
}

/* Scalar arrays */

obj lean_copy_sarray(obj a, size_t cap) {
    unsigned esz = lean_sarray_elem_size(a);
    size_t sz = lean_sarray_size(a);
    if (cap < sz) cap = sz;
    obj r = lean_alloc_sarray(esz, sz, cap);
    memcpy(lean_sarray_cptr(r), lean_sarray_cptr(a), sz * esz);
    lean_dec(a);
    return r;
}

obj lean_copy_sarray_nonlinear(obj a, size_t cap) { return lean_copy_sarray(a, cap); }

bool lean_sarray_eq_cold(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    return memcmp(lean_sarray_cptr(a1), lean_sarray_cptr(a2),
                  lean_sarray_size(a1) * lean_sarray_elem_size(a1)) == 0;
}

obj lean_byte_array_push(obj a, uint8_t b) {
    obj r = a;
    if (!lean_is_exclusive(a) || lean_sarray_size(a) == lean_sarray_capacity(a))
        r = lean_copy_sarray(a, (lean_sarray_capacity(a) + 1) * 2);
    lean_sarray_object *o = (lean_sarray_object *)r;
    o->m_data[o->m_size++] = b;
    return r;
}

obj lean_byte_array_mk(obj arr) {
    size_t n = lean_array_size(arr);
    obj r = lean_alloc_sarray(1, n, n);
    for (size_t i = 0; i < n; i++) lean_sarray_cptr(r)[i] = (uint8_t)lean_unbox(lean_array_get_core(arr, i));
    lean_dec(arr);
    return r;
}

obj lean_byte_array_data(obj a) {
    size_t n = lean_sarray_size(a);
    obj r = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++) lean_array_cptr(r)[i] = lean_box(lean_sarray_cptr(a)[i]);
    lean_dec(a);
    return r;
}

obj lean_byte_array_copy_slice(b_lean_obj_arg src, obj o_src_off, obj dest, obj o_dest_off, obj o_len,
                               uint8_t exact) {
    size_t ssz = lean_sarray_size(src);
    size_t dsz = lean_sarray_size(dest);
    size_t src_off = lean_is_scalar(o_src_off) ? lean_unbox(o_src_off) : ssz;
    if (src_off > ssz) src_off = ssz;
    size_t len = lean_is_scalar(o_len) ? lean_unbox(o_len) : ssz;
    if (len > ssz - src_off) len = ssz - src_off;
    size_t dest_off = lean_is_scalar(o_dest_off) ? lean_unbox(o_dest_off) : dsz;
    if (dest_off > dsz) dest_off = dsz;
    size_t new_size = dest_off + len > dsz ? dest_off + len : dsz;
    obj r = dest;
    if (!lean_is_exclusive(dest) || new_size > lean_sarray_capacity(dest))
        r = lean_copy_sarray(dest, exact ? new_size : (new_size > 2 * dsz ? new_size : 2 * dsz));
    lean_to_sarray(r)->m_size = new_size;
    memmove(lean_sarray_cptr(r) + dest_off, lean_sarray_cptr(src) + src_off, len);
    return r;
}

uint64_t lean_byte_array_hash(b_lean_obj_arg a) {
    uint64_t h = 11;
    for (size_t i = 0; i < lean_sarray_size(a); i++) h = h * 31 + lean_sarray_cptr(a)[i];
    return h;
}

/* ------------------------------------------------------------------------ */
/* Strings                                                                   */

static size_t utf8_len(const char *s, size_t n) {
    size_t len = 0;
    for (size_t i = 0; i < n; i++) if (((unsigned char)s[i] & 0xC0) != 0x80) len++;
    return len;
}

size_t lean_utf8_strlen(char const *str) { return utf8_len(str, strlen(str)); }
size_t lean_utf8_n_strlen(char const *str, size_t n) { return utf8_len(str, n); }

obj lean_mk_string_unchecked(char const *s, size_t sz, size_t len) {
    obj r = lean_alloc_string(sz + 1, sz + 1, len);
    memcpy(lean_to_string(r)->m_data, s, sz);
    lean_to_string(r)->m_data[sz] = 0;
    return r;
}
obj lean_mk_string_from_bytes(char const *s, size_t sz) { return lean_mk_string_unchecked(s, sz, utf8_len(s, sz)); }
obj lean_mk_string_from_bytes_unchecked(char const *s, size_t sz) { return lean_mk_string_from_bytes(s, sz); }
obj lean_mk_ascii_string_unchecked(char const *s) { size_t n = strlen(s); return lean_mk_string_unchecked(s, n, n); }
obj lean_mk_string(char const *s) { return lean_mk_string_from_bytes(s, strlen(s)); }

obj lean_copy_string(obj s, size_t cap) {
    size_t sz = lean_string_size(s);
    if (cap < sz) cap = sz;
    obj r = lean_alloc_string(sz, cap, lean_string_len(s));
    memcpy(lean_to_string(r)->m_data, lean_string_cstr(s), sz);
    lean_dec(s);
    return r;
}
obj lean_copy_string_nonlinear(obj s, size_t cap) { return lean_copy_string(s, cap); }

static obj string_reserve(obj s, size_t extra) {
    size_t need = lean_string_size(s) + extra;
    if (lean_is_exclusive(s) && lean_string_capacity(s) >= need) return s;
    return lean_copy_string(s, need + need / 2);
}

obj lean_string_append(obj s1, b_lean_obj_arg s2) {
    size_t n2 = lean_string_size(s2) - 1;
    if (n2 == 0) return s1;
    size_t n1 = lean_string_size(s1) - 1;
    size_t len2 = lean_string_len(s2);
    obj r = string_reserve(s1, n2);
    lean_string_object *o = lean_to_string(r);
    memcpy(o->m_data + n1, lean_string_cstr(s2), n2 + 1);
    o->m_size = n1 + n2 + 1;
    o->m_length += len2;
    return r;
}

static unsigned utf8_encode(uint32_t c, char *out) {
    if (c < 0x80) { out[0] = (char)c; return 1; }
    if (c < 0x800) { out[0] = (char)(0xC0 | (c >> 6)); out[1] = (char)(0x80 | (c & 0x3F)); return 2; }
    if (c < 0x10000) {
        out[0] = (char)(0xE0 | (c >> 12)); out[1] = (char)(0x80 | ((c >> 6) & 0x3F));
        out[2] = (char)(0x80 | (c & 0x3F)); return 3;
    }
    out[0] = (char)(0xF0 | (c >> 18)); out[1] = (char)(0x80 | ((c >> 12) & 0x3F));
    out[2] = (char)(0x80 | ((c >> 6) & 0x3F)); out[3] = (char)(0x80 | (c & 0x3F)); return 4;
}

static uint32_t utf8_decode(const unsigned char *s, size_t *i) {
    unsigned c = s[*i];
    if (c < 0x80) { *i += 1; return c; }
    if ((c & 0xE0) == 0xC0) { uint32_t r = ((c & 0x1F) << 6) | (s[*i + 1] & 0x3F); *i += 2; return r; }
    if ((c & 0xF0) == 0xE0) {
        uint32_t r = ((c & 0x0F) << 12) | ((s[*i + 1] & 0x3F) << 6) | (s[*i + 2] & 0x3F); *i += 3; return r;
    }
    uint32_t r = ((c & 0x07) << 18) | ((s[*i + 1] & 0x3F) << 12) | ((s[*i + 2] & 0x3F) << 6) | (s[*i + 3] & 0x3F);
    *i += 4;
    return r;
}

obj lean_string_push(obj s, uint32_t c) {
    char buf[4];
    unsigned k = utf8_encode(c, buf);
    obj r = string_reserve(s, k);
    lean_string_object *o = lean_to_string(r);
    memcpy(o->m_data + o->m_size - 1, buf, k);
    o->m_size += k;
    o->m_data[o->m_size - 1] = 0;
    o->m_length++;
    return r;
}

obj lean_string_mk(obj cs) {
    obj r = lean_mk_string_unchecked("", 0, 0);
    for (obj l = cs; !lean_is_scalar(l); l = lean_ctor_get(l, 1))
        r = lean_string_push(r, lean_unbox_uint32(lean_ctor_get(l, 0)));
    lean_dec(cs);
    return r;
}

obj lean_string_data(obj s) {
    const unsigned char *p = (const unsigned char *)lean_string_cstr(s);
    size_t n = lean_string_size(s) - 1;
    /* build the list back to front */
    size_t count = lean_string_len(s);
    uint32_t stackbuf[64];
    uint32_t *cps = stackbuf;
    obj tmp = NULL;
    if (count > 64) { tmp = lean_alloc_sarray(4, count, count); cps = (uint32_t *)lean_sarray_cptr(tmp); }
    size_t i = 0, k = 0;
    while (i < n && k < count) cps[k++] = utf8_decode(p, &i);
    obj r = lean_box(0);
    while (k-- > 0) {
        obj c = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(c, 0, lean_box_uint32(cps[k]));
        lean_ctor_set(c, 1, r);
        r = c;
    }
    if (tmp) lean_dec(tmp);
    lean_dec(s);
    return r;
}

obj lean_string_to_utf8(b_lean_obj_arg s) {
    size_t n = lean_string_size(s) - 1;
    obj r = lean_alloc_sarray(1, n, n);
    memcpy(lean_sarray_cptr(r), lean_string_cstr(s), n);
    return r;
}

bool lean_string_eq_cold(b_lean_obj_arg s1, b_lean_obj_arg s2) {
    return memcmp(lean_string_cstr(s1), lean_string_cstr(s2), lean_string_size(s1)) == 0;
}

bool lean_string_lt(b_lean_obj_arg s1, b_lean_obj_arg s2) {
    size_t n1 = lean_string_size(s1) - 1, n2 = lean_string_size(s2) - 1;
    int c = memcmp(lean_string_cstr(s1), lean_string_cstr(s2), n1 < n2 ? n1 : n2);
    return c < 0 || (c == 0 && n1 < n2);
}

uint8_t lean_string_compare(b_lean_obj_arg s1, b_lean_obj_arg s2) {
    if (lean_string_lt(s1, s2)) return 0;
    if (lean_string_size(s1) == lean_string_size(s2) && lean_string_eq_cold(s1, s2)) return 1;
    return 2;
}

uint64_t lean_string_hash(b_lean_obj_arg s) {
    uint64_t h = 7;
    const char *p = lean_string_cstr(s);
    for (size_t i = 0; i + 1 < lean_string_size(s); i++) h = h * 31 + (unsigned char)p[i];
    return h;
}

uint32_t lean_string_utf8_get(b_lean_obj_arg s, b_lean_obj_arg i0) {
    if (!lean_is_scalar(i0)) return 'A';
    size_t i = lean_unbox(i0), n = lean_string_size(s) - 1;
    if (i >= n) return 'A';  /* `default : Char` */
    return utf8_decode((const unsigned char *)lean_string_cstr(s), &i);
}

uint32_t lean_string_utf8_get_fast_cold(char const *str, size_t i, size_t size, unsigned char c) {
    (void)size; (void)c;
    return utf8_decode((const unsigned char *)str, &i);
}

obj lean_string_utf8_next(b_lean_obj_arg s, b_lean_obj_arg i0) {
    if (!lean_is_scalar(i0)) return lean_nat_add(i0, lean_box(1));
    size_t i = lean_unbox(i0), n = lean_string_size(s) - 1;
    if (i >= n) return lean_box(i + 1);
    utf8_decode((const unsigned char *)lean_string_cstr(s), &i);
    return lean_box(i);
}

obj lean_string_utf8_next_fast_cold(size_t i, unsigned char c) {
    if ((c & 0xE0) == 0xC0) return lean_box(i + 2);
    if ((c & 0xF0) == 0xE0) return lean_box(i + 3);
    return lean_box(i + 4);
}

obj lean_string_utf8_prev(b_lean_obj_arg s, b_lean_obj_arg i0) {
    if (!lean_is_scalar(i0)) return lean_box(0);
    size_t i = lean_unbox(i0);
    if (i == 0) return lean_box(0);
    const char *p = lean_string_cstr(s);
    if (i > lean_string_size(s) - 1) i = lean_string_size(s);
    i--;
    while (i > 0 && (((unsigned char)p[i]) & 0xC0) == 0x80) i--;
    return lean_box(i);
}

obj lean_string_utf8_extract(b_lean_obj_arg s, b_lean_obj_arg b0, b_lean_obj_arg e0) {
    size_t n = lean_string_size(s) - 1;
    size_t b = lean_is_scalar(b0) ? lean_unbox(b0) : n, e = lean_is_scalar(e0) ? lean_unbox(e0) : n;
    if (e > n) e = n;
    if (b >= e) return lean_mk_string_unchecked("", 0, 0);
    return lean_mk_string_from_bytes(lean_string_cstr(s) + b, e - b);
}

obj lean_string_of_usize(size_t n) {
    char buf[24];
    int k = 0;
    do { buf[k++] = (char)('0' + n % 10); n /= 10; } while (n);
    char out[24];
    for (int i = 0; i < k; i++) out[i] = buf[k - 1 - i];
    return lean_mk_string_unchecked(out, (size_t)k, (size_t)k);
}

/* ------------------------------------------------------------------------ */
/* Numbers: Nat < 2^64 and Int in [-2^63, 2^63) beyond the boxed range       */

typedef struct {
    lean_object m_header;
    uint64_t mag;
    uint8_t neg;
} small_mpz;

static obj mk_mpz(uint64_t mag, bool neg) {
    small_mpz *o = (small_mpz *)lean_alloc_small_object(sizeof(small_mpz));
    lean_set_st_header((lean_object *)o, LeanMPZ, 0);
    o->mag = mag;
    o->neg = neg && mag != 0;
    return (obj)o;
}

static inline void nat_get(b_lean_obj_arg a, uint64_t *m) {
    *m = lean_is_scalar(a) ? (uint64_t)lean_unbox(a) : ((small_mpz *)a)->mag;
}

static obj nat_of_u64(uint64_t v) {
    return v <= LEAN_MAX_SMALL_NAT ? lean_box((size_t)v) : mk_mpz(v, false);
}

static inline void int_get(b_lean_obj_arg a, bool *neg, uint64_t *m) {
    if (lean_is_scalar(a)) {
        int64_t v = lean_scalar_to_int64(a);
        *neg = v < 0;
        *m = v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
    } else {
        *neg = ((small_mpz *)a)->neg;
        *m = ((small_mpz *)a)->mag;
    }
}

static obj int_of(bool neg, uint64_t m) {
    if (m == 0) return lean_box(0);
    if (!neg && m <= (uint64_t)LEAN_MAX_SMALL_INT) return lean_int64_to_int((int64_t)m);
    if (neg && m <= (uint64_t)0 - (uint64_t)(int64_t)LEAN_MIN_SMALL_INT) return lean_int64_to_int(-(int64_t)m);
    if (m > (uint64_t)INT64_MAX + (neg ? 1u : 0u)) fatal("uvl: Int beyond 64 bits");
    return mk_mpz(m, neg);
}

static uint64_t add_ck(uint64_t a, uint64_t b) {
    uint64_t r;
    if (__builtin_add_overflow(a, b, &r)) fatal("uvl: Nat beyond 64 bits");
    return r;
}
static uint64_t mul_ck(uint64_t a, uint64_t b) {
    uint64_t r;
    if (__builtin_mul_overflow(a, b, &r)) fatal("uvl: Nat beyond 64 bits");
    return r;
}

obj lean_big_usize_to_nat(size_t n) { return mk_mpz(n, false); }
obj lean_big_uint64_to_nat(uint64_t n) { return mk_mpz(n, false); }
obj lean_big_int_to_int(int n) { return int_of(n < 0, n < 0 ? (uint64_t)0 - (uint64_t)(int64_t)n : (uint64_t)n); }
obj lean_big_size_t_to_int(size_t n) { return int_of(false, n); }
obj lean_big_int64_to_int(int64_t n) { return int_of(n < 0, n < 0 ? (uint64_t)0 - (uint64_t)n : (uint64_t)n); }

obj lean_cstr_to_nat(char const *s) {
    uint64_t v = 0;
    for (; *s; s++) v = add_ck(mul_ck(v, 10), (uint64_t)(*s - '0'));
    return nat_of_u64(v);
}

obj lean_cstr_to_int(char const *s) {
    bool neg = *s == '-';
    if (neg) s++;
    uint64_t v = 0;
    for (; *s; s++) v = add_ck(mul_ck(v, 10), (uint64_t)(*s - '0'));
    return int_of(neg, v);
}

/* Big literals, interned and persistent (see fix_literals in uvl_bundle.py):
   the generated code never releases them, which is only correct if they live
   forever. Distinct literal values are few, so the table stays tiny. */
#define LITERALS 64
static struct { uint64_t mag; bool neg; obj o; } literals[LITERALS];
static unsigned n_literals;

static obj intern(uint64_t mag, bool neg, obj o) {
    if (lean_is_scalar(o)) return o;
    for (unsigned i = 0; i < n_literals; i++)
        if (literals[i].mag == mag && literals[i].neg == neg) { lean_dec(o); return literals[i].o; }
    lean_mark_persistent(o);
    if (n_literals < LITERALS) {
        literals[n_literals].mag = mag; literals[n_literals].neg = neg; literals[n_literals].o = o;
        n_literals++;
    }
    return o;
}

obj uvl_nat_literal(char const *s) {
    uint64_t v = 0;
    for (const char *p = s; *p; p++) v = add_ck(mul_ck(v, 10), (uint64_t)(*p - '0'));
    return intern(v, false, nat_of_u64(v));
}

obj uvl_int_literal(char const *s) {
    bool neg = *s == '-';
    uint64_t v = 0;
    for (const char *p = s + neg; *p; p++) v = add_ck(mul_ck(v, 10), (uint64_t)(*p - '0'));
    return intern(v, neg, int_of(neg, v));
}

#define NAT2(a1, a2) uint64_t x, y; nat_get(a1, &x); nat_get(a2, &y)
obj lean_nat_big_succ(obj a) { uint64_t x; nat_get(a, &x); return nat_of_u64(add_ck(x, 1)); }
obj lean_nat_big_add(obj a1, obj a2) { NAT2(a1, a2); return nat_of_u64(add_ck(x, y)); }
obj lean_nat_big_sub(obj a1, obj a2) { NAT2(a1, a2); return nat_of_u64(x > y ? x - y : 0); }
obj lean_nat_big_mul(obj a1, obj a2) { NAT2(a1, a2); return nat_of_u64(mul_ck(x, y)); }
obj lean_nat_overflow_mul(size_t a1, size_t a2) { return nat_of_u64(mul_ck(a1, a2)); }
obj lean_nat_big_div(obj a1, obj a2) { NAT2(a1, a2); return nat_of_u64(y == 0 ? 0 : x / y); }
obj lean_nat_big_div_exact(obj a1, obj a2) { return lean_nat_big_div(a1, a2); }
obj lean_nat_big_mod(obj a1, obj a2) { NAT2(a1, a2); return nat_of_u64(y == 0 ? x : x % y); }
bool lean_nat_big_eq(obj a1, obj a2) { NAT2(a1, a2); return x == y; }
bool lean_nat_big_le(obj a1, obj a2) { NAT2(a1, a2); return x <= y; }
bool lean_nat_big_lt(obj a1, obj a2) { NAT2(a1, a2); return x < y; }
obj lean_nat_big_land(obj a1, obj a2) { NAT2(a1, a2); return nat_of_u64(x & y); }
obj lean_nat_big_lor(obj a1, obj a2) { NAT2(a1, a2); return nat_of_u64(x | y); }
obj lean_nat_big_xor(obj a1, obj a2) { NAT2(a1, a2); return nat_of_u64(x ^ y); }

obj lean_nat_shiftl(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    NAT2(a1, a2);
    if (x == 0) return lean_box(0);
    if (y >= 64 || (x >> (64 - y)) != 0) fatal("uvl: Nat beyond 64 bits");
    return nat_of_u64(x << y);
}
obj lean_nat_big_shiftr(b_lean_obj_arg a1, b_lean_obj_arg a2) { NAT2(a1, a2); return nat_of_u64(y >= 64 ? 0 : x >> y); }

obj lean_nat_pow(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    NAT2(a1, a2);
    uint64_t r = 1;
    while (y--) r = mul_ck(r, x);
    return nat_of_u64(r);
}

obj lean_nat_log2(b_lean_obj_arg a) {
    uint64_t x; nat_get(a, &x);
    unsigned r = 0;
    while (x >>= 1) r++;
    return lean_box(r);
}

obj lean_nat_gcd(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    NAT2(a1, a2);
    while (y) { uint64_t t = x % y; x = y; y = t; }
    return nat_of_u64(x);
}

uint8_t lean_uint8_of_big_nat(b_lean_obj_arg a) { uint64_t x; nat_get(a, &x); return (uint8_t)x; }
uint16_t lean_uint16_of_big_nat(b_lean_obj_arg a) { uint64_t x; nat_get(a, &x); return (uint16_t)x; }
uint32_t lean_uint32_of_big_nat(b_lean_obj_arg a) { uint64_t x; nat_get(a, &x); return (uint32_t)x; }
uint64_t lean_uint64_of_big_nat(b_lean_obj_arg a) { uint64_t x; nat_get(a, &x); return x; }
size_t lean_usize_of_big_nat(b_lean_obj_arg a) { uint64_t x; nat_get(a, &x); return (size_t)x; }

#define INT2(a1, a2) bool n1, n2; uint64_t x, y; int_get(a1, &n1, &x); int_get(a2, &n2, &y)

static obj int_add(bool n1, uint64_t x, bool n2, uint64_t y) {
    if (n1 == n2) return int_of(n1, add_ck(x, y));
    if (x >= y) return int_of(n1, x - y);
    return int_of(n2, y - x);
}

obj lean_int_big_neg(obj a) { bool n; uint64_t m; int_get(a, &n, &m); return int_of(!n, m); }
obj lean_int_big_add(obj a1, obj a2) { INT2(a1, a2); return int_add(n1, x, n2, y); }
obj lean_int_big_sub(obj a1, obj a2) { INT2(a1, a2); return int_add(n1, x, !n2, y); }
obj lean_int_big_mul(obj a1, obj a2) { INT2(a1, a2); return int_of(n1 != n2, mul_ck(x, y)); }
/* `Int.div`: rounds toward zero */
obj lean_int_big_div(obj a1, obj a2) { INT2(a1, a2); return y == 0 ? lean_box(0) : int_of(n1 != n2, x / y); }
obj lean_int_big_div_exact(obj a1, obj a2) { return lean_int_big_div(a1, a2); }
/* `Int.mod`: sign of the dividend */
obj lean_int_big_mod(obj a1, obj a2) { INT2(a1, a2); return y == 0 ? int_of(n1, x) : int_of(n1, x % y); }
/* `Int.ediv` / `Int.emod`: Euclidean, remainder always ≥ 0 */
obj lean_int_big_ediv(obj a1, obj a2) {
    INT2(a1, a2);
    if (y == 0) return lean_box(0);
    uint64_t q = x / y, r = x % y;
    if (!n1) return int_of(n2, q);
    return int_of(!n2, r ? q + 1 : q);
}
obj lean_int_big_emod(obj a1, obj a2) {
    INT2(a1, a2);
    if (y == 0) return int_of(n1, x);
    uint64_t r = x % y;
    return int_of(false, (n1 && r) ? y - r : r);
}
static int int_cmp(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    INT2(a1, a2);
    if (x == 0) n1 = false;
    if (y == 0) n2 = false;
    if (n1 != n2) return n1 ? -1 : 1;
    int c = x < y ? -1 : (x > y ? 1 : 0);
    return n1 ? -c : c;
}
bool lean_int_big_eq(obj a1, obj a2) { return int_cmp(a1, a2) == 0; }
bool lean_int_big_le(obj a1, obj a2) { return int_cmp(a1, a2) <= 0; }
bool lean_int_big_lt(obj a1, obj a2) { return int_cmp(a1, a2) < 0; }
bool lean_int_big_nonneg(obj a) { bool n; uint64_t m; int_get(a, &n, &m); return !n || m == 0; }

/* Int → Nat (`Int.toNat`) for big values. */
obj lean_big_int_to_nat(obj a) {
    bool n; uint64_t m; int_get(a, &n, &m);
    lean_dec(a);
    return n ? lean_box(0) : nat_of_u64(m);
}

uint8_t lean_float_isnan(double a) { return a != a; }
uint8_t lean_float_isinf(double a) { return a == a && a - a != a - a; }
uint8_t lean_float_isfinite(double a) { return a - a == a - a; }

/* Int -> IntN wraps modulo 2^N, like the reference runtime. */
int64_t lean_int64_of_big_int(b_lean_obj_arg a) {
    bool neg; uint64_t m; int_get(a, &neg, &m);
    return (int64_t)(neg ? (uint64_t)0 - m : m);
}
int32_t lean_int32_of_big_int(b_lean_obj_arg a) { return (int32_t)lean_int64_of_big_int(a); }
int16_t lean_int16_of_big_int(b_lean_obj_arg a) { return (int16_t)lean_int64_of_big_int(a); }
int8_t lean_int8_of_big_int(b_lean_obj_arg a) { return (int8_t)lean_int64_of_big_int(a); }

double lean_float_of_bits(uint64_t u) { double d; memcpy(&d, &u, sizeof d); return d; }
uint64_t lean_float_to_bits(double d) { uint64_t u; memcpy(&u, &d, sizeof u); return u; }

/* ------------------------------------------------------------------------ */
/* Platform                                                                  */

obj lean_system_platform_nbits(obj unit) { (void)unit; return lean_box(sizeof(void *) * 8); }
