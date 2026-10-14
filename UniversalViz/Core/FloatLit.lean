import Lean

/-!
# Fast `Float` literals

Lean elaborates a literal such as `0.5 : Float` to `Float.ofScientific 5 true 1`,
which the compiler does not constant-fold: every evaluation runs arbitrary
precision arithmetic. Inside a rasterizer's per-pixel loop that dominated the
profile (over half of all instructions).

This elaborator turns `Float` scientific literals into `Float.ofBits n`, where
`n` is the IEEE-754 bit pattern computed at compile time; `Float.ofBits` is a
free reinterpretation at runtime. The value is identical.
-/

namespace UViz.FloatLit

open Lean Elab Term Meta

elab_rules : term <= expectedType
  | `($x:scientific) => do
    tryPostponeIfMVar expectedType
    let ty ← whnfR expectedType
    unless ty.isConstOf ``Float do throwUnsupportedSyntax
    let some (m, s, e) := x.raw.isScientificLit? | throwUnsupportedSyntax
    return mkApp (mkConst ``Float.ofBits) (toExpr (Float.ofScientific m s e).toBits)

end UViz.FloatLit
