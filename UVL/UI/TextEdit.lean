import UVL.Text.Layout
import UVL.Layout.Placed

/-!
# Text editing

The state of an editable text (`TextInput`) and how input events change it.
It is shared by the single-line `textField` and the multi-line `textArea`
(`UI/Controls.lean`); the difference between the two is only their
`TextLayout`: one line, or lines wrapped to a width and split at `'\n'`.

Positions are character indices `0..n`. The selection runs from `anchor` to
`cursor`, in either order.
-/

namespace UVL.UI

open Layout

/-! ### Layout of editable text -/

/-- One visual line: characters `[start, stop)` of the text, without the
`'\n'` that ends a paragraph. A `soft` line was wrapped and continues on the
next line (its trailing space is part of it). -/
structure TextLine where
  start : Nat
  stop : Nat
  soft : Bool
deriving Inhabited, Repr

/-- Lines of an editable text and the pen position of every cursor position in
each line (pixels from the line start). -/
structure TextLayout where
  lines : Array TextLine
  stops : Array (Array Float)
  lineHeight : Float
deriving Inhabited

private def ofChars (cs : List Char) : String := cs.foldl String.push ""

/-- Pen positions of every cursor position `0..n` of a single line, in pixels. -/
def textStops (font : Text.Font) (size : Float) (s : String) : Array Float :=
  let (gs, w) := Text.shape font s
  (gs.map (·.x * size)).push (w * size)

namespace TextLayout

/-- Lay out `s`: split at `'\n'`, and when `wrap` is set break lines greedily
after spaces so that none is wider than `maxWidth` pixels (a longer word is
broken anywhere). -/
def make (font : Text.Font) (size : Float) (s : String) (wrap : Bool := false)
    (maxWidth : Float := 0) : TextLayout := Id.run do
  let mut lines : Array TextLine := #[]
  let mut stops : Array (Array Float) := #[]
  let mut base := 0
  for para in s.splitOn "\n" do
    let cs := para.toList.toArray
    let m := cs.size
    let mut ls := 0
    if wrap then
      let p := textStops font size para
      let mut brk := 0
      for i in [0:m] do
        if p[i + 1]! - p[ls]! > maxWidth && i > ls then
          let cut := if brk > ls then brk else i
          lines := lines.push { start := base + ls, stop := base + cut, soft := true }
          ls := cut
        if cs[i]! == ' ' then brk := i + 1
    lines := lines.push { start := base + ls, stop := base + m, soft := false }
    base := base + m + 1
  -- per-line stops (kerning restarts at line breaks)
  let chars := s.toList.toArray
  for l in lines do
    stops := stops.push (textStops font size (ofChars (chars.extract l.start l.stop).toList))
  return { lines, stops, lineHeight := font.lineHeight * size }

/-- The line showing cursor position `c`: the last one starting at or before
it (so the end of a soft line shows at the start of the next). -/
def lineOf (t : TextLayout) (c : Nat) : Nat := Id.run do
  let mut k := 0
  for i in [0:t.lines.size] do
    if t.lines[i]!.start ≤ c then k := i
  return k

/-- Pen position of cursor position `c` within its line. -/
def xOf (t : TextLayout) (c : Nat) : Float :=
  let k := t.lineOf c
  (t.stops[k]?.bind (·[c - t.lines[k]!.start]?)).getD 0

/-- Top of cursor position `c`'s line, from the top of the text. -/
def yOf (t : TextLayout) (c : Nat) : Float := (t.lineOf c).toFloat * t.lineHeight

/-- Last cursor position that shows on line `k` (before a soft line's
trailing space, which would show on the next line). -/
def lineEnd' (t : TextLayout) (k : Nat) : Nat :=
  let l := t.lines[k]!
  if l.soft && l.stop > l.start then l.stop - 1 else l.stop

/-- The cursor position on line `k` nearest to `x`. -/
def atX (t : TextLayout) (k : Nat) (x : Float) : Nat := Id.run do
  let ps := t.stops[k]!
  let mut best := 0
  for i in [0:ps.size] do
    if (ps[i]! - x).abs < (ps[best]! - x).abs then best := i
  return Min.min (t.lines[k]!.start + best) (t.lineEnd' k)

/-- The cursor position nearest to `(x, y)`, in pixels from the top-left
corner of the text. -/
def hit (t : TextLayout) (x y : Float) : Nat :=
  if t.lines.isEmpty then 0 else
  let k := if y ≤ 0 then 0 else Min.min (t.lines.size - 1) (y / t.lineHeight).floor.toUInt64.toNat
  t.atX k x

def lineStart (t : TextLayout) (c : Nat) : Nat := t.lines[t.lineOf c]!.start
def lineEnd (t : TextLayout) (c : Nat) : Nat := t.lineEnd' (t.lineOf c)

/-- The cursor position one line up (or down) at the same horizontal position;
past the first (last) line, the start (end) of the text. -/
def vertical (t : TextLayout) (c : Nat) (up : Bool) : Nat :=
  let k := t.lineOf c
  let x := t.xOf c
  if up then (if k == 0 then 0 else t.atX (k - 1) x)
  else if k + 1 ≥ t.lines.size then t.lines.back!.stop else t.atX (k + 1) x

end TextLayout

/-! ### Words -/

/-- Character classes for word navigation: spaces, word characters, other. -/
private def charClass (c : Char) : Nat :=
  if c == ' ' || c == '\n' || c == '\t' then 0
  else if c.isAlphanum || c == '_' || c.toNat ≥ 128 then 1 else 2

/-- Start of the word before position `c` (Ctrl+Left): skip spaces, then a run
of one class. -/
def wordLeft (cs : Array Char) (c : Nat) : Nat := Id.run do
  let mut i := Min.min c cs.size
  while i > 0 && charClass cs[i - 1]! == 0 do i := i - 1
  if i == 0 then return 0
  let k := charClass cs[i - 1]!
  while i > 0 && charClass cs[i - 1]! == k do i := i - 1
  return i

/-- End of the word after position `c` (Ctrl+Right). -/
def wordRight (cs : Array Char) (c : Nat) : Nat := Id.run do
  let mut i := Min.min c cs.size
  while i < cs.size && charClass cs[i]! == 0 do i := i + 1
  if i ≥ cs.size then return cs.size
  let k := charClass cs[i]!
  while i < cs.size && charClass cs[i]! == k do i := i + 1
  return i

/-- The word (or run of spaces or punctuation) around position `c`, for
double-click selection. -/
def wordAt (cs : Array Char) (c : Nat) : Nat × Nat := Id.run do
  if cs.isEmpty then return (0, 0)
  let c := Min.min c (cs.size - 1)
  -- prefer the character before the position when the one after is a space
  let c := if c > 0 && charClass cs[c]! == 0 && charClass cs[c - 1]! != 0 then c - 1 else c
  let k := charClass cs[c]!
  let mut a := c
  while a > 0 && charClass cs[a - 1]! == k do a := a - 1
  let mut b := c + 1
  while b < cs.size && charClass cs[b]! == k do b := b + 1
  return (a, b)

/-! ### State -/

/-- The state of an editable text: contents, cursor (in characters), selection
anchor, focus, and the vertical scroll of a text area (pixels). The selection
runs from `anchor` to `cursor` (either order); `anchor = none` means nothing is
selected. -/
structure TextInput where
  text : String := ""
  cursor : Nat := 0
  anchor : Option Nat := none
  focused : Bool := false
  scroll : Float := 0
  /-- Earlier `(text, cursor)` states, most recent first (Ctrl+Z). -/
  undo : List (String × Nat) := []
  /-- Undone states (Ctrl+Y / Ctrl+Shift+Z). -/
  redo : List (String × Nat) := []
  /-- Kind of the last edit (0: none or a cursor move, 1: typing, 2: deleting
  characters), so that a run of keystrokes is undone as one step. -/
  lastEdit : Nat := 0
deriving Inhabited, Repr

namespace TextInput

/-- Field-by-field equality (written out: see `Runtime.sameTarget`). -/
def same (a b : TextInput) : Bool :=
  a.text == b.text && a.cursor == b.cursor && a.focused == b.focused && a.scroll == b.scroll &&
    a.lastEdit == b.lastEdit &&
    match a.anchor, b.anchor with
    | some x, some y => x == y
    | none, none => true
    | _, _ => false

/-- The selected character range `[start, stop)`, if any. -/
def selection? (st : TextInput) : Option (Nat × Nat) :=
  match st.anchor with
  | some a => if a == st.cursor then none else some (Min.min a st.cursor, Max.max a st.cursor)
  | none => none

/-- The selected text. -/
def selectedText (st : TextInput) : String :=
  match st.selection? with
  | some (a, b) => ofChars ((st.text.toList.drop a).take (b - a))
  | none => ""

/-- Replace characters `[a, b)` by `ins`, leaving the cursor after it. -/
def splice (st : TextInput) (a b : Nat) (ins : List Char) : TextInput :=
  let cs := st.text.toList
  { st with text := ofChars (cs.take a ++ ins ++ cs.drop b), cursor := a + ins.length,
            anchor := none }

/-- Delete the selection (if any). -/
def deleteSelection (st : TextInput) : TextInput :=
  match st.selection? with
  | some (a, b) => st.splice a b []
  | none => { st with anchor := none }

/-- Move the cursor to `c`, extending the selection or dropping it. -/
def moveTo (st : TextInput) (c : Nat) (extend : Bool) : TextInput :=
  { st with cursor := c, anchor := if extend then some (st.anchor.getD st.cursor) else none }

/-- Where a movement key takes cursor position `c`. -/
def move (lay : TextLayout) (n c : Nat) : Key → Nat
  | .left => c - 1
  | .right => Min.min n (c + 1)
  | .up => lay.vertical c true
  | .down => lay.vertical c false
  | .home => lay.lineStart c
  | .end_ => lay.lineEnd c
  | _ => c

def isMove : Key → Bool
  | .left | .right | .up | .down | .home | .end_ => true
  | _ => false

/-- Characters that may be typed: printable ones, plus `'\n'` when
`multiline`. -/
def typeable (multiline : Bool) (c : Char) : Bool :=
  (c.toNat ≥ 32 && c.toNat != 127) || (multiline && c == '\n')

/-- Scroll so that the cursor's line is inside a view `h` pixels tall (no-op
for `h = 0`). -/
def keepVisible (st : TextInput) (lay : TextLayout) (h : Float) : TextInput :=
  if h ≤ 0 then st else
  let top := lay.yOf st.cursor
  let maxScroll := Max.max 0 (lay.lines.size.toFloat * lay.lineHeight - h)
  let s := Min.min st.scroll maxScroll
  let s := if top < s then top else if top + lay.lineHeight > s + h then top + lay.lineHeight - h else s
  { st with scroll := Max.max 0 s }

/-- Most undo steps kept. -/
def historyLimit : Nat := 100

/-- Go back to the previous state of the undo history (or forward again with
`redo := true`). -/
def travel (st : TextInput) (redo : Bool) : TextInput :=
  match (if redo then st.redo else st.undo) with
  | (t, c) :: rest =>
    let here := (st.text, st.cursor)
    if redo then { st with text := t, cursor := c, anchor := none, redo := rest,
                           undo := here :: st.undo, lastEdit := 0 }
    else { st with text := t, cursor := c, anchor := none, undo := rest,
                   redo := here :: st.redo, lastEdit := 0 }
  | [] => st

/-- Record the edit from `old` to `st` (of kind `kind`) in the undo history:
a new step, unless it continues a run of the same kind of keystrokes. -/
def record (st old : TextInput) (kind : Nat) : TextInput :=
  if kind != 0 && kind == old.lastEdit then { st with redo := [] }
  else { st with undo := ((old.text, old.cursor) :: old.undo).take historyLimit, redo := [],
                 lastEdit := kind }

/-- Apply an input event. `layout` lays out a text (the current one, or the
edited one); pointer positions are in pixels from the top-left corner of the
text, scroll included. `viewHeight` is the visible height of the text, used to
keep the cursor in view. -/
def apply (st : TextInput) (layout : String → TextLayout) (multiline : Bool := false)
    (viewHeight : Float := 0) (ev : InputEvent) : TextInput :=
  let lay := layout st.text
  let cs := st.text.toList.toArray
  let n := cs.size
  let c := Min.min st.cursor n
  let st' : TextInput := match ev with
    | .focus => { st with focused := true }
    | .blur => { st with focused := false, anchor := none }
    | .press x y => let p := lay.hit x y; { st with cursor := p, anchor := some p }
    | .drag x y => st.moveTo (lay.hit x y) true
    | .doubleClick x y =>
      let (a, b) := wordAt cs (lay.hit x y)
      { st with anchor := some a, cursor := b }
    | .selectAll => { st with anchor := some 0, cursor := n }
    | .undo => st.travel false
    | .redo => st.travel true
    | .wheel dy =>
      let maxScroll := Max.max 0 (lay.lines.size.toFloat * lay.lineHeight - viewHeight)
      if viewHeight ≤ 0 then st else { st with scroll := Max.max 0 (Min.min maxScroll (st.scroll + dy)) }
    | .cut => st.deleteSelection
    | .text s =>
      let ins := (s.toList.map fun ch => if ch == '\r' then '\n' else ch).filter (typeable multiline)
      if ins.isEmpty then st else
      match st.selection? with
      | some (a, b) => st.splice a b ins
      | none => st.splice c c ins
    | .extend k => st.moveTo (move lay n c k) true
    | .word k extend =>
      match k, st.selection? with
      | .backspace, some _ | .delete, some _ => st.deleteSelection
      | .backspace, none => st.splice (wordLeft cs c) c []
      | .delete, none => st.splice c (wordRight cs c) []
      | .left, _ => st.moveTo (wordLeft cs c) extend
      | .right, _ => st.moveTo (wordRight cs c) extend
      | .home, _ => st.moveTo 0 extend
      | .end_, _ => st.moveTo n extend
      | _, _ => st
    | .key k =>
      match k, st.selection? with
      | .backspace, some _ | .delete, some _ => st.deleteSelection
      | .backspace, none => if c == 0 then st else st.splice (c - 1) c []
      | .delete, none => if c ≥ n then st else st.splice c (c + 1) []
      | .enter, _ =>
        if multiline then let d := st.deleteSelection; d.splice d.cursor d.cursor ['\n'] else st
      -- with a selection, Left/Right collapse it to its start/end
      | .left, some (a, _) => { st with cursor := a, anchor := none }
      | .right, some (_, b) => { st with cursor := b, anchor := none }
      | k, _ => if isMove k then st.moveTo (move lay n c k) false else st
  -- undo history
  let st' := match ev with
    | .undo | .redo | .focus | .blur | .wheel _ => st'
    | _ =>
      if st'.text != st.text then
        let kind := match ev, st.selection? with
          | .text s, none => if s.length == 1 then 1 else 0
          | .key .backspace, none | .key .delete, none => 2
          | _, _ => 0
        st'.record st kind
      else if st'.cursor != st.cursor then { st' with lastEdit := 0 } else st'
  match ev with
  | .wheel _ => st'
  | _ => st'.keepVisible (layout st'.text) viewHeight

end TextInput

end UVL.UI
