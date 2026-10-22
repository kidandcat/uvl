/*
 * Hand-written stubs for the Android build.
 *
 * `lean_initialize` initializes the whole Lean compiler and lives in the `Lean`
 * package, which an app does not link; only programs that elaborate Lean code
 * at runtime need it.
 */
#include <lean/lean.h>

void lean_initialize(void) {}

/*
 * `Lean.Meta.inferType` is `@[extern "lean_infer_type"]`, implemented in the
 * Lean compiler (`Lean.Meta.inferTypeImp`). The HTML elaborator calls it while
 * compiling markup, so the generated C references the symbol, but an app does
 * not link the compiler and never elaborates at run time. Same policy as
 * `lean_initialize`: panic if it is ever actually called.
 */
lean_object *lean_infer_type(lean_object *e, lean_object *lctx, lean_object *localInsts,
                             lean_object *cfg, lean_object *mctx) {
  (void)e; (void)lctx; (void)localInsts; (void)cfg; (void)mctx;
  lean_internal_panic("compile-time-only symbol called: lean_infer_type");
}
