/*
 * Bare-metal replacement for the toolchain's <lean/config.h>.
 *
 * Put `baremetal/include` *before* the toolchain's include directory: the stock
 * <lean/lean.h> (the ABI the generated C is written against) then picks up this
 * configuration instead of the desktop one:
 *
 *   - no mimalloc: lean.h's small-object path calls malloc / free_sized, which
 *     are redirected below to the static pool in uvl_rt.c (no system heap);
 *   - 32-bit targets (Cortex-M, Xtensa, RISC-V): 8-byte scalar literals in
 *     static closed terms must expand to two pointer-sized words.
 */
#pragma once
#include <lean/version.h>

#define LEAN_IS_STAGE0 0
#if !defined(FLT_EVAL_METHOD) || (FLT_EVAL_METHOD != 0)
#error Lean requires `FLT_EVAL_METHOD = 0` to ensure predictable semantics for floating-point operations.
#endif

#if UINTPTR_MAX == 0xffffffffu
/* lean.h only uses LEAN_EMSCRIPTEN to split 64-bit scalar literals into two
   32-bit words; that is exactly what every 32-bit target needs. */
#define LEAN_EMSCRIPTEN
#endif

#define malloc     uvl_heap_alloc
#define free_sized uvl_heap_free
#define free       uvl_heap_free_unsized
