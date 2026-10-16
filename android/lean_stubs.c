/*
 * Hand-written stubs for the Android build.
 *
 * `lean_initialize` initializes the whole Lean compiler and lives in the `Lean`
 * package, which an app does not link; only programs that elaborate Lean code
 * at runtime need it.
 */
#include <lean/lean.h>

void lean_initialize(void) {}
