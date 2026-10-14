/*
 * Borrowing wrappers around the functions an app exports from Lean
 * (`@[export uvl_*]`), so firmware code never deals with reference counts.
 */
#include <lean/lean.h>
#include <string.h>
#include "uvl.h"

static size_t copy_out(lean_object *bytes, uint8_t *out, size_t cap) {
    size_t n = lean_sarray_size(bytes);
    if (n > cap) n = cap;
    memcpy(out, lean_sarray_cptr(bytes), n);
    lean_dec(bytes);
    return n;
}

size_t uvl_render_tile_rgb565(uvl_state s, uint16_t tx, uint16_t ty, uint8_t *out, size_t cap) {
    lean_inc((lean_object *)s);
    return copy_out((lean_object *)uvl_tile_rgb565(s, tx, ty), out, cap);
}

size_t uvl_render_tile_mono(uvl_state s, uint16_t tx, uint16_t ty, uint8_t *out, size_t cap) {
    lean_inc((lean_object *)s);
    return copy_out((lean_object *)uvl_tile_mono(s, tx, ty), out, cap);
}

int uvl_redraw_pending(uvl_state s) {
    lean_inc((lean_object *)s);
    return uvl_needs_redraw(s) != 0;
}

void uvl_state_free(uvl_state s) { lean_dec((lean_object *)s); }
