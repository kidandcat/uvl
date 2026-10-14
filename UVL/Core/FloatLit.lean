import Lean

/-!
# Fast `Float` literals

Lean elaborates a literal such as `0.5 : Float` to `Float.ofScientific 5 true 1`,
which the compiler does not constant-fold: every evaluation runs arbitrary
precision arithmetic. Inside a rasterizer's per-pixel loop that dominated the
profile (over half of all instructions).

This elaborator turns `Float` scientific literals into `Float.ofBits n`, where
`n` is the IEEE-754 bit pattern computed at compile time; `Float.ofBits` is a
free reinterpretation at runtime. The value is identical. Natural number
literals at type `Float` (`2 : Float`) get the same treatment.

`Nat.toF` is the runtime counterpart for converting naturals: `Nat.toFloat`
also goes through `Float.ofScientific`, which rebuilds the big number `2 ^ 53`
on every call (from a decimal string, via GMP). That alone was ~40% of the
instructions of a frame.
-/

namespace UVL.FloatLit

open Lean Elab Term Meta

elab_rules : term <= expectedType
  | `($x:scientific) => do
    tryPostponeIfMVar expectedType
    let ty ← whnfR expectedType
    unless ty.isConstOf ``Float do throwUnsupportedSyntax
    let some (m, s, e) := x.raw.isScientificLit? | throwUnsupportedSyntax
    return mkApp (mkConst ``Float.ofBits) (toExpr (Float.ofScientific m s e).toBits)

/-- `n : Float` for a numeral `n`; any other numeral falls through to Lean's
own elaborator (also when the expected type is unknown). -/
@[term_elab num] def elabFloatNum : TermElab := fun stx expectedType? => do
  -- never postpone: binop% elaborates numerals before their type is known
  let some ty := expectedType? | throwUnsupportedSyntax
  let ty ← whnfR (← instantiateMVars ty)
  unless ty.isConstOf ``Float do throwUnsupportedSyntax
  let some n := stx.isNatLit? | throwUnsupportedSyntax
  return mkApp (mkConst ``Float.ofBits) (toExpr (Float.ofNat n).toBits)

end UVL.FloatLit

/-- Convert a natural number to the nearest `Float`, like `Nat.toFloat`, but
with a cast instead of arbitrary precision arithmetic for `n < 2 ^ 30` (every
pixel coordinate). -/
@[inline] def Nat.toF (n : Nat) : Float :=
  if n < 1073741824 then n.toUInt64.toFloat else n.toFloat
