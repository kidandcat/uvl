/*
 * Hand-written stubs for the standalone WebAssembly build.
 *
 * The Lean runtime normally links against libuv and the `Lean` package. The
 * browser build links neither: libuv is only used for file-system error
 * messages here, and `lean_initialize` (which initializes the whole compiler)
 * is only needed by programs that elaborate Lean code at runtime.
 *
 * Symbols from `Lean`/`Std` that are referenced only by compile-time code
 * (elaborators, `bv_decide` reflection terms) get generated stubs; see
 * web/build.sh.
 */
#include <lean/lean.h>

void lean_initialize(void) {}

/*
 * See android/lean_stubs.c: the HTML elaborator references `lean_infer_type`
 * (`Lean.Meta.inferType`). The compiler is not linked into the wasm module.
 */
lean_object *lean_infer_type(lean_object *e, lean_object *lctx, lean_object *localInsts,
                             lean_object *cfg, lean_object *mctx) {
  (void)e; (void)lctx; (void)localInsts; (void)cfg; (void)mctx;
  lean_internal_panic("compile-time-only symbol called: lean_infer_type");
}

const char *uv_strerror(int err) {
  (void)err;
  return "I/O error";
}

/*
 * Fast `Nat.toFloat` for wasm32. Init's `Float.ofNat` goes through
 * `Float.ofScientific`, which compares against `2 ^ 53`: a big number on a
 * 32-bit target, so every conversion allocates. App code is compiled with
 * `-Dlean_float_of_nat=uvl_float_of_nat` (see web/build.sh); small naturals
 * convert exactly with a cast, anything else takes the original path.
 */
double lean_float_of_nat(lean_object *n);

double uvl_float_of_nat(lean_object *n) {
  if (lean_is_scalar(n)) return (double)lean_unbox(n);
  return lean_float_of_nat(n);
}
