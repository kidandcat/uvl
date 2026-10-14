import Lean
import UniversalViz.UI.Basic

/-!
# `ui!` — indentation-based declarative syntax

```
ui! col (gap := 12):
  text "Hola" (size := 3)
  row: text "Lean"; button "Click"
  spacer
```

Each line is `name args*` or `name args* :` followed by an indented block of
children (or `;`-separated on the same line). `name` resolves to `UViz.UI.name`,
named arguments are passed through, and the children become the final `List`
argument — so `ui!` is pure sugar over the function API and adding a new widget
only requires defining a function.
-/

namespace UViz.UI.DSL

open Lean

declare_syntax_cat uiw
syntax uiArg := ppSpace colGt (Lean.Parser.Term.namedArgument <|> term:max)
syntax uiBlock := sepBy1IndentSemicolon(uiw)
syntax ident uiArg* : uiw
syntax ident uiArg* ":" uiBlock : uiw
syntax "ui! " uiw : term

def mkApp (f : Ident) (args : Array (TSyntax `UViz.UI.DSL.uiArg)) (extra : Array Term) :
    MacroM Term := do
  let fn := mkIdentFrom f (`UViz.UI ++ f.getId)
  let argStx := args.map (·.raw[0]) ++ extra.map (·.raw)
  if argStx.isEmpty then return fn
  return ⟨mkNode ``Lean.Parser.Term.app #[fn, mkNullNode argStx]⟩

macro_rules
  | `(ui! $f:ident $args:uiArg*) => mkApp f args #[]
  | `(ui! $f:ident $args:uiArg* : $b:uiBlock) => do
    let ws : Array (TSyntax `uiw) := b.raw[0].getSepArgs.map (⟨·⟩)
    let kids ← ws.mapM fun w => `(ui! $w)
    mkApp f args #[← `([$kids,*])]

end UViz.UI.DSL
