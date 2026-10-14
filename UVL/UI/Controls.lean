import UVL.UI.Label
import UVL.UI.TextEdit

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

/-! ### Text field and text area -/

/-- The editor shared by `textField` and `textArea`: `width × height` pixels,
text inset by 8 pixels. -/
def textEditor (id : String) (st : TextInput) (onChange : TextInput → Msg)
    (width height : Nat) (size : Float) (placeholder : String) (onSubmit : Option Msg)
    (font : Text.Font) (color : Color) (multiline : Bool) : Widget Msg :=
  let pad := 8.0
  let innerW := width.toFloat - 2 * pad
  let innerH := height.toFloat - 2 * pad
  let layout := fun s => TextLayout.make font size s (wrap := multiline) (maxWidth := innerW)
  let lay := layout st.text
  let lh := lay.lineHeight
  let shiftX := if multiline then 0 else Max.max 0 (lay.xOf st.cursor - innerW + 2)
  let scrollY := if multiline then st.scroll else 0
  let chars := st.text.toList.toArray
  let clipTo (r : Rect) (ops : Array RenderOp) : Array RenderOp :=
    #[.clip (if multiline then ⟨r.x + pad - 1, r.y + 2, innerW + 2, r.h - 4⟩
             else ⟨r.x + pad - 1, r.y, innerW + 2, r.h⟩) ops]
  let field := canvas width height fun r =>
    let ox := r.x + pad - shiftX
    let oy := r.y + pad - scrollY
    let visible (k : Nat) := oy + (k + 1).toFloat * lh > r.y && oy + k.toFloat * lh < r.y + r.h
    let box := r.inflate (-0.5)
    let frame : Array RenderOp :=
      #[.fill (.roundedRect box (.all 6)) Color.white,
        if st.focused then .stroke (.roundedRect (r.inflate (-1)) (.all 6)) 2 color
        else .stroke (.roundedRect box (.all 6)) 1 (Color.hex 0xB0BEC5)]
    let highlight : Array RenderOp := match st.selection? with
      | some (a, b) =>
        let sel := if st.focused then color.withAlpha 0.25 else Color.hex 0xCFD8DC
        (List.range lay.lines.size).foldl (init := #[]) fun acc k =>
          let l := lay.lines[k]!
          let s := Max.max a l.start
          let e := Min.min b l.stop
          -- a selected line break shows as a little extra width
          let nl := if b > l.stop && !l.soft then size * 0.3 else 0
          if (s > e || (s == e && nl == 0)) || !visible k then acc else
          let ps := lay.stops[k]!
          let x0 := (ox + ps[s - l.start]!).round
          let x1 := (ox + ps[e - l.start]! + nl).round
          acc.push (.fill (.rect ⟨x0, oy + k.toFloat * lh, x1 - x0, lh⟩) sel)
      | none => #[]
    let textOps :=
      if st.text.isEmpty then
        Text.linesOps font #[placeholder] size (Color.hex 0x90A4AE) ⟨r.x + pad, r.y + pad⟩
      else (List.range lay.lines.size).foldl (init := #[]) fun acc k =>
        let l := lay.lines[k]!
        if !visible k then acc else
        acc ++ Text.linesOps font #[(chars.extract l.start l.stop).foldl String.push ""] size
          (Color.hex 0x263238) ⟨ox, oy + k.toFloat * lh⟩
    frame ++ clipTo r (highlight ++ textOps)
  let caret := canvas width height fun r =>
    let x := (r.x + pad - shiftX + lay.xOf st.cursor).round
    clipTo r #[.fill (.rect ⟨x - 0.5, r.y + pad - scrollY + lay.yOf st.cursor, 1.5, lh⟩) color]
  .action (.input id (selection := st.selectedText) fun ev =>
      match ev, onSubmit with
      | .key .enter, some m => some m
      | _, _ =>
        -- pointer positions relative to the text
        let tx (x : Float) := x - pad + shiftX
        let ty (y : Float) := y - pad + scrollY
        let ev := match ev with
          | .press x y => .press (tx x) (ty y)
          | .drag x y => .drag (tx x) (ty y)
          | .doubleClick x y => .doubleClick (tx x) (ty y)
          | ev => ev
        let st' := st.apply layout multiline (if multiline then innerH else 0) ev
        if st'.same st then none else some (onChange st'))
    (if st.focused then .stack .start .start [field, .blink caret] else field)

/-- A single-line text field with id `id` (for keyboard focus). It dispatches
`onChange` with the new state on every edit, cursor or selection change and
focus change, and `onSubmit` on Enter.

Text is selected by dragging, double-clicking a word, Shift+click,
Shift+arrows and Ctrl+A; Ctrl+arrows move by words and Ctrl+Backspace deletes
one. Ctrl+C, Ctrl+X and pasting go through the system clipboard. The caret
blinks. -/
def textField (id : String) (st : TextInput) (onChange : TextInput → Msg)
    (width : Nat := 240) (size : Float := 16) (placeholder : String := "")
    (onSubmit : Option Msg := none) (font : Text.Font := Text.uvlSans ())
    (color : Color := Color.hex 0x1E88E5) : Widget Msg :=
  let height := (font.lineHeight * size + 16).ceil.toUInt64.toNat
  textEditor id st onChange width height size placeholder onSubmit font color false

/-- A multi-line text area `lines` lines tall: text wraps at the width and at
`'\n'` (Enter), Up/Down move between lines, Home/End go to the line's ends
and Ctrl+Home/End to the text's, and the contents scroll to keep the cursor in
view. Editing and selection work as in `textField`. -/
def textArea (id : String) (st : TextInput) (onChange : TextInput → Msg)
    (width : Nat := 320) (lines : Nat := 4) (size : Float := 16) (placeholder : String := "")
    (font : Text.Font := Text.uvlSans ()) (color : Color := Color.hex 0x1E88E5) : Widget Msg :=
  let height := (lines.toFloat * font.lineHeight * size + 16).ceil.toUInt64.toNat
  textEditor id st onChange width height size placeholder none font color true

/-! ### Scroll view -/

/-- A vertical scroll view `height` pixels tall (0: as tall as its parent
allows); `offset` comes from the model and the wheel dispatches
`onScroll newOffset`. -/
def scrollView (offset : Nat) (onScroll : Nat → Msg) (child : Widget Msg)
    (height : Nat := 0) : Widget Msg :=
  let v := Widget.scroll offset onScroll child
  if height == 0 then v else .sized none (some height) v

end UVL.UI
