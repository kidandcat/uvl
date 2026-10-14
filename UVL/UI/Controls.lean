import UVL.UI.Label

/-!
# Stateful controls

Sliders, checkboxes, text fields and scroll views. Their state lives in the
application's model (Elm style): each control is drawn from that state and
dispatches a message carrying the new state, which `update` stores.

```
structure Model where
  volume : Float := 0.5
  name : TextInput := {}
  scroll : Nat := 0

col [ slider m.volume .setVolume,
      textField "name" m.name .editName (placeholder := "Your name"),
      scrollView m.scroll .scrolled (height := 200) longList ]
```

The runtime does the rest: it captures the pointer while a slider is dragged,
gives the keyboard to the focused field (click, Tab, Escape), and routes the
wheel to the scroll view under the pointer.
-/

namespace UVL.UI

open Layout

variable {Msg : Type}

@[inline] private def clamp01 (x : Float) : Float := Min.min 1 (Max.max 0 x)

/-! ### Slider -/

/-- A horizontal slider for `value ∈ [lo, hi]`; pressing or dragging sets the
value under the pointer. -/
def slider (value : Float) (onChange : Float → Msg) (lo : Float := 0) (hi : Float := 1)
    (width : Nat := 200) (color : Color := Color.hex 0x1E88E5) : Widget Msg :=
  let t := clamp01 ((value - lo) / (hi - lo))
  .action (.drag fun p =>
      if p.phase == .release then none
      else some (onChange (lo + (hi - lo) * clamp01 ((p.x - 10) / (p.w - 20)))))
    (canvas width 24 fun r =>
      let x0 := r.x + 10
      let x1 := r.x + r.w - 10
      let cy := r.y + r.h / 2
      let tx := x0 + (x1 - x0) * t
      #[.fill (.roundedRect ⟨x0, cy - 2, x1 - x0, 4⟩ (.all 2)) (Color.hex 0xCFD8DC),
        .fill (.roundedRect ⟨x0, cy - 2, tx - x0, 4⟩ (.all 2)) color,
        .shadow ⟨tx - 8, cy - 8, 16, 16⟩ 8 3 (Color.black.withAlpha 0.3),
        .fill (.circle ⟨tx, cy⟩ 8) Color.white,
        .stroke (.circle ⟨tx, cy⟩ 7) 2 color])

/-! ### Checkbox -/

/-- A checkbox with a label; tapping it dispatches `onToggle`. -/
def checkbox (checked : Bool) (onToggle : Msg) (text : String := "") (size : Float := 16)
    (color : Color := Color.hex 0x1E88E5) : Widget Msg :=
  let box := canvas 18 18 fun r =>
    if checked then
      #[.fill (.roundedRect r (.all 4)) color,
        .stroke (.path ({ : Path }.moveTo (r.x + 4) (r.y + 9.5) |>.lineTo (r.x + 7.5) (r.y + 13)
          |>.lineTo (r.x + 14) (r.y + 5))) 2.2 Color.white]
    else
      #[.fill (.roundedRect r (.all 4)) Color.white,
        .stroke (.roundedRect (r.inflate (-0.75)) (.all 3.5)) 1.5 (Color.hex 0x90A4AE)]
  onTap onToggle (radius := 4) <|
    if text.isEmpty then box else row (gap := 8) [box, label text size]

/-! ### Text field -/

/-- The state of a text field: contents, cursor (in characters) and focus. -/
structure TextInput where
  text : String := ""
  cursor : Nat := 0
  focused : Bool := false
deriving Inhabited, Repr, BEq

namespace TextInput

private def ofChars (cs : List Char) : String := cs.foldl String.push ""

/-- Pen positions of every cursor position `0..n`, in pixels. -/
def stops (font : Text.Font) (size : Float) (s : String) : Array Float :=
  let (gs, w) := Text.shape font s
  (gs.map (·.x * size)).push (w * size)

/-- Horizontal shift of the contents so that the cursor stays visible in a
field `inner` pixels wide. -/
def shift (st : TextInput) (font : Text.Font) (size inner : Float) : Float :=
  let cx := (stops font size st.text)[st.cursor]?.getD 0
  Max.max 0 (cx - inner + 2)

/-- The cursor position nearest to `x` pixels from the start of the text. -/
def cursorAt (font : Text.Font) (size : Float) (s : String) (x : Float) : Nat := Id.run do
  let ps := stops font size s
  let mut best := 0
  for i in [0:ps.size] do
    if (ps[i]! - x).abs < (ps[best]! - x).abs then best := i
  return best

/-- Apply an input event; `inner` is the width available to the text. -/
def apply (st : TextInput) (font : Text.Font) (size inner : Float) : InputEvent → TextInput
  | .focus => { st with focused := true }
  | .blur => { st with focused := false }
  | .press x _ => { st with cursor := cursorAt font size st.text (x + st.shift font size inner) }
  | .text s =>
    let ins := s.toList.filter fun c => c.toNat ≥ 32 && c.toNat != 127
    let cs := st.text.toList
    { st with text := ofChars (cs.take st.cursor ++ ins ++ cs.drop st.cursor),
              cursor := st.cursor + ins.length }
  | .key k =>
    let cs := st.text.toList
    let n := cs.length
    let c := Min.min st.cursor n
    match k with
    | .backspace =>
      if c == 0 then st
      else { st with text := ofChars (cs.take (c - 1) ++ cs.drop c), cursor := c - 1 }
    | .delete => if c ≥ n then st else { st with text := ofChars (cs.take c ++ cs.drop (c + 1)) }
    | .left => { st with cursor := c - 1 }
    | .right => { st with cursor := Min.min n (c + 1) }
    | .home => { st with cursor := 0 }
    | .end_ => { st with cursor := n }
    | _ => st

end TextInput

/-- A single-line text field with id `id` (for keyboard focus). It dispatches
`onChange` with the new state on every edit, cursor move and focus change, and
`onSubmit` on Enter. -/
def textField (id : String) (st : TextInput) (onChange : TextInput → Msg)
    (width : Nat := 240) (size : Float := 16) (placeholder : String := "")
    (onSubmit : Option Msg := none) (font : Text.Font := Text.uvlSans ())
    (color : Color := Color.hex 0x1E88E5) : Widget Msg :=
  let pad := 8.0
  let inner := width.toFloat - 2 * pad
  let lineH := font.lineHeight * size
  let height := (lineH + 2 * pad).ceil.toUInt64.toNat
  .action (.input id fun ev =>
      match ev, onSubmit with
      | .key .enter, some m => some m
      | _, _ =>
        let st' := st.apply font size inner ev
        if st' == st then none else some (onChange st'))
    (canvas width height fun r =>
      let shift := st.shift font size inner
      let box := r.inflate (-0.5)
      let frame : Array RenderOp :=
        #[.fill (.roundedRect box (.all 6)) Color.white,
          if st.focused then .stroke (.roundedRect (r.inflate (-1)) (.all 6)) 2 color
          else .stroke (.roundedRect box (.all 6)) 1 (Color.hex 0xB0BEC5)]
      let textOps :=
        if st.text.isEmpty then
          Text.linesOps font #[placeholder] size (Color.hex 0x90A4AE) ⟨r.x + pad, r.y + pad⟩
        else Text.linesOps font #[st.text] size (Color.hex 0x263238) ⟨r.x + pad - shift, r.y + pad⟩
      let caret : Array RenderOp :=
        if st.focused then
          let cx := (TextInput.stops font size st.text)[st.cursor]?.getD 0
          #[.fill (.rect ⟨(r.x + pad - shift + cx).round - 0.5, r.y + pad, 1.5, lineH⟩) color]
        else #[]
      frame ++ #[.clip ⟨r.x + pad - 1, r.y, inner + 2, r.h⟩ (textOps ++ caret)])

/-! ### Scroll view -/

/-- A vertical scroll view `height` pixels tall (0: as tall as its parent
allows); `offset` comes from the model and the wheel dispatches
`onScroll newOffset`. -/
def scrollView (offset : Nat) (onScroll : Nat → Msg) (child : Widget Msg)
    (height : Nat := 0) : Widget Msg :=
  let v := Widget.scroll offset onScroll child
  if height == 0 then v else .sized none (some height) v

end UVL.UI
