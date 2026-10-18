import Lean
import UVL.UI.Basic

/-!
# HTML-like markup

Widgets written as tags, JSX style:

```
<col gap=14 align=.stretch>
  <label size=24 color={accent}>Controls</label>
  <slider value={m.volume} onChange={.volume} width=180/>
  <button size=4 onTap={.inc}>+</button>
  {meter m.meter.value}
  <card>
    <label>{n} words, {chars} characters</label>
  </card>
</col>
```

It is compile-time syntax over the function API, not HTML: there is no
parser, DOM or CSS at run time, and every tag elaborates to the same calls you
would write by hand, so it runs everywhere UVL does (web, desktop, Android and
bare metal) and every mistake is a type error.

* `<f a=v …>` calls `UVL.UI.f`, or `f` itself when there is no such widget, so
  your own functions are tags too. Each attribute is a named argument
  `(a := v)`; a bare attribute `<label msdf …>` means `(a := true)`.
* Attribute values are a string, a number, a constructor (`.stretch`), a name
  or any term in braces: `color={Color.hex 0x0D47A1}`. When the parameter is
  an `Option`, the value is wrapped in `some` if needed: `onTap={.inc}`.
* The content between the tags is passed as the first explicit parameter not
  given as an attribute, by its type: text (with `{x}` interpolated through
  `toString`) for a `String` (`<label>`, `<button>`, `<checkbox>`), the
  children for a `List` (`<col>`, `<row>`, `<stack>`), and for a single
  `Widget` (`<card>`, `<pad>`, `<expanded>`) one child as is, several as a
  column.
* A `{e}` child is a `Widget`, or an `Option`, `List` or `Array` of widgets,
  which is spliced in: `{items.map fun s => <label>{s}</label>}`.
-/

namespace UVL.UI

namespace Html

open Lean Parser

def htmlTextFn : ParserFn := fun c s =>
  let startPos := s.pos
  let s := takeWhile1Fn (fun ch => ch != '<' && ch != '>' && ch != '{' && ch != '}')
    "expected text" c s
  mkNodeToken `UVL.UI.Html.htmlText startPos true c s

/-- Text between tags: anything up to `<`, `>`, `{` or `}`. (A bare `{ fn }`:
this constant is initialized when an app starts, where the parser library is
not linked, so it must not call into it.) -/
def htmlText : Parser := { fn := htmlTextFn }

open PrettyPrinter in
@[combinator_formatter htmlText] def htmlText.formatter : Formatter := pure ()
open PrettyPrinter in
@[combinator_parenthesizer htmlText] def htmlText.parenthesizer : Parenthesizer := pure ()

declare_syntax_cat htmlElement
declare_syntax_cat htmlChild

syntax htmlAttrVal := str <|> num <|> scientific <|> ("{" term "}") <|> ("." ident) <|> ident
syntax htmlAttr := ident ("=" htmlAttrVal)?

syntax atomic("<" noWs ident) htmlAttr* "/>" : htmlElement
syntax atomic("<" noWs ident) htmlAttr* ">" htmlChild* "</" ident ">" : htmlElement

syntax htmlText : htmlChild
syntax "{" term "}" : htmlChild
syntax htmlElement : htmlChild

syntax:max htmlElement : term

/-- `htmlOpt% v`: `v`, or `some v` when the expected type is an `Option` and
`v` does not have it. -/
syntax "htmlOpt% " term:max : term

/-- `htmlKids% list (text)?`: the children as the expected type asks — the
`List` itself, `ofList` of it for a single widget, or the text for a
`String`. -/
syntax "htmlKids% " term:max (term:max)? : term

/-- `htmlKid% e`: a `{e}` child as a list of children — `[e]` for a widget,
or the `List`, `Array` or `Option` of widgets `e` is. -/
syntax "htmlKid% " term:max : term

open Elab Term Meta

elab_rules : term <= ty
  | `(htmlOpt% $v) => do
    -- wait for the widget's `Msg` so that `.ctor` values can be resolved
    if (← instantiateMVars ty).hasMVar then tryPostpone
    let ty ← whnfR (← instantiateMVars ty)
    unless ty.isAppOf ``Option do return ← elabTermEnsuringType v ty
    let s ← saveState
    -- `.ctor` fails right away against `Option`; other values coerce to it
    try withoutErrToSorry <| elabTermEnsuringType v ty
    catch _ =>
      s.restore
      elabTermEnsuringType (← `(some $v)) ty

elab_rules : term <= ty
  | `(htmlKids% $list $[$text]?) => do
    tryPostponeIfMVar ty
    let ty ← whnfR (← instantiateMVars ty)
    if ty.isAppOf ``String then
      match text with
      | some t => elabTermEnsuringType t ty
      | none => throwError "this content is text, but it contains elements"
    else if ty.isAppOf ``List || ty.isMVar then elabTermEnsuringType list ty
    else elabTermEnsuringType (← `(UVL.UI.ofList $list)) ty

elab_rules : term <= ty
  | `(htmlKid% $e) => do
    let ty ← whnfR (← instantiateMVars ty)
    let some w := (if ty.isAppOfArity ``List 1 then some ty.appArg! else none)
      | throwError "a child is expected to be a list of widgets, not{indentExpr ty}"
    -- elaborate first, then look at the type: the widgets' `Msg` comes from `ty`
    let v ← elabTerm e none
    let vTy ← instantiateMVars (← inferType v)
    if ← isDefEq vTy w then return ← mkListLit w [v]
    if ← isDefEq vTy ty then return v
    if ← isDefEq vTy (← mkAppM ``Array #[w]) then return ← mkAppM ``Array.toList #[v]
    if ← isDefEq vTy (← mkAppM ``Option #[w]) then return ← mkAppM ``Option.toList #[v]
    throwError "a `\{…}` child must be a widget, or a list, array or option of widgets; \
      it has type{indentExpr vTy}"

/-- Collapse whitespace runs to one space (text inside tags reads like HTML). -/
private def collapse (s : String) : String := Id.run do
  let mut out := ""
  let mut ws := false
  for c in s.toList do
    if c.isWhitespace then ws := true
    else
      if ws then out := out.push ' '
      ws := false
      out := out.push c
  if ws then out := out.push ' '
  return out

private def hasTrailingSpace (stx : Syntax) : Bool :=
  match stx.getTailInfo.getTrailing? with
  | some t => !t.isEmpty
  | none => false

/-- One piece of a tag's content. -/
private inductive Piece where
  | text (s : String)
  | expr (t : Term)
  | elem (t : Term)

/-- The tag name as a term: the widget `UVL.UI.f` if it exists, else `f`. -/
private def tagFn (f : Ident) : MacroM Term := do
  let full := `UVL.UI ++ f.getId
  if !(← Macro.resolveGlobalName full).isEmpty then return mkIdentFrom f full
  return f

private def attrArg (a : TSyntax ``htmlAttr) : MacroM Syntax := do
  let name : Ident := ⟨a.raw[0]⟩
  let val : Term ←
    if a.raw[1].getNumArgs == 0 then `(true) else
      -- by shape: quotation patterns do not compare atoms such as `{` and `.`
      let v := a.raw[1][1][0]
      if v.getKind == groupKind && v[0].getAtomVal == "{" then pure ⟨v[1]⟩
      else if v.getKind == groupKind then
        pure ⟨mkNode ``Lean.Parser.Term.dotIdent #[v[0], v[1]]⟩
      else pure ⟨v⟩
  `(Lean.Parser.Term.namedArgument| ($name := htmlOpt% ($val)))

/-- Build the content argument from the children, if there are any. -/
private def content (kids : Array (TSyntax `htmlChild)) : MacroM (Option Term) := do
  if kids.isEmpty then return none
  let mut pieces : Array Piece := #[]
  for k in kids do
    -- (no quotation patterns here: `htmlText` would read their text)
    let c := k.raw[0]
    if c.getKind == `UVL.UI.Html.htmlText then
      pieces := pieces.push (.text (c.isLit? `UVL.UI.Html.htmlText).get!)
    else if c.isAtom then
      pieces := pieces.push (.expr ⟨k.raw[1]⟩)
    else
      pieces := pieces.push (.elem ⟨c⟩)
    if hasTrailingSpace k.raw then pieces := pieces.push (.text " ")
  let isText := pieces.any fun | .text s => !s.all Char.isWhitespace | _ => false
  let isElem := pieces.any fun | .elem _ => true | _ => false
  -- the children as a `List`
  let mut acc : Option Term := none
  for p in pieces do
    let part ← match p with
      | .elem t => some <$> `([$t])
      | .expr t => some <$> `(htmlKid% $t)
      | .text _ => pure none
    if let some part := part then
      acc ← match acc with
        | none => pure part
        | some l => some <$> `($l ++ $part)
  let list ← match acc with | some l => pure l | none => `([])
  -- the children as text: merge adjacent literals, trim the ends
  let mut strs : Array (Sum String Term) := #[]
  for p in pieces do
    match p with
    | .text s =>
      match strs.back? with
      | some (.inl t) => strs := strs.pop.push (.inl (t ++ s))
      | _ => strs := strs.push (.inl s)
    | .expr t => strs := strs.push (.inr t)
    | .elem _ => pure ()
  strs := strs.map fun | .inl s => .inl (collapse s) | x => x
  if let some (Sum.inl s) := strs[0]? then strs := strs.set! 0 (.inl (String.ofList (s.toList.dropWhile Char.isWhitespace)))
  if let some (Sum.inl s) := strs.back? then strs := strs.pop.push (.inl (String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse))
  let mut accT : Option Term := none
  for s in strs do
    let part ← match s with
      | .inl s => if s.isEmpty then pure none else some <$> `($(quote s))
      | .inr t => some <$> `(toString $t)
    if let some part := part then
      accT ← match accT with
        | none => pure part
        | some l => some <$> `($l ++ $part)
  let text ← match accT with | some t => pure t | none => `("")
  if isText then
    if isElem then
      Macro.throwErrorAt kids[0]! "text and elements cannot be mixed: wrap the text in <label>"
    return some text
  if isElem then return some (← `(htmlKids% $list))
  return some (← `(htmlKids% $list $text))

private def mkCall (f : Ident) (attrs : Array (TSyntax ``htmlAttr)) (arg : Option Term) :
    MacroM Term := do
  let fn ← tagFn f
  let args := (← attrs.mapM attrArg) ++ (arg.map (·.raw)).toArray
  if args.isEmpty then return fn
  return ⟨mkNode ``Lean.Parser.Term.app #[fn, mkNullNode args]⟩

macro_rules
  | `($e:htmlElement) => pure e.raw

macro_rules
  | `(htmlElement| <$f:ident $attrs:htmlAttr* />) => mkCall f attrs none
  | `(htmlElement| <$f:ident $attrs:htmlAttr* > $kids:htmlChild* </$g:ident >) => do
    unless f.getId == g.getId do
      Macro.throwErrorAt g s!"expected </{f.getId}>"
    mkCall f attrs (← content kids)

end Html

end UVL.UI
