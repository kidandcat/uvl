import Lean
import UVL.UI.Basic

/-!
# `ui!` — indentation-based declarative syntax

```
ui! col (gap := 12):
  text "Hola" (size := 3)
  row: text "Lean"; button "Click"
  spacer
```

Each line is `name args*` or `name args* :` followed by an indented block of
children (or `;`-separated on the same line). `name` resolves to `UVL.UI.name`,
named arguments are passed through, and the children become the final `List`
argument — so `ui!` is pure sugar over the function API and adding a new widget
only requires defining a function.
-/

namespace UVL.UI.DSL

open Lean

declare_syntax_cat uiw
syntax uiArg := ppSpace colGt (Lean.Parser.Term.namedArgument <|> term:max)
syntax uiBlock := sepBy1IndentSemicolon(uiw)
syntax ident uiArg* : uiw
syntax ident uiArg* ":" uiBlock : uiw
syntax "ui! " uiw : term

def mkApp (f : Ident) (args : Array (TSyntax `UVL.UI.DSL.uiArg)) (extra : Array Term) :
    MacroM Term := do
  let fn := mkIdentFrom f (`UVL.UI ++ f.getId)
  let argStx := args.map (·.raw[0]) ++ extra.map (·.raw)
  if argStx.isEmpty then return fn
  return ⟨mkNode ``Lean.Parser.Term.app #[fn, mkNullNode argStx]⟩

/-- `uiAlt% a | b` elaborates `a`, or `b` if `a` fails. Used to pass a block
either as a `List` (containers) or as a single widget (wrappers). -/
syntax "uiAlt% " term " | " term : term

open Elab Term in
elab_rules : term <= ty
  | `(uiAlt% $a | $b) => do
    let s ← saveState
    try
      let e ← withoutErrToSorry <| elabTermEnsuringType a ty
      synthesizeSyntheticMVarsNoPostponing
      return e
    catch _ =>
      s.restore
      elabTermEnsuringType b ty

macro_rules
  | `(ui! $f:ident $args:uiArg*) => mkApp f args #[]
  | `(ui! $f:ident $args:uiArg* : $b:uiBlock) => do
    let ws : Array (TSyntax `uiw) := b.raw[0].getSepArgs.map (⟨·⟩)
    let kids ← ws.mapM fun w => `(ui! $w)
    let asList ← mkApp f args #[← `([$kids,*])]
    let asOne ← mkApp f args #[← `(UVL.UI.ofList [$kids,*])]
    `(uiAlt% $asList | $asOne)

end UVL.UI.DSL
