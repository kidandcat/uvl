import UVL

/-! Interactive example: stateful controls (slider, checkboxes, text field and
a scroll view, a multi-line text area), with all their state in the model (Elm
architecture), and a level meter that follows the slider with a tween. -/

namespace Examples.Controls
open UVL UI

inductive Msg where
  | volume (v : Float)
  | toggle (i : Nat)
  | name (st : TextInput)
  | submit
  | scrolled (offset : Nat)
  | pick (i : Nat)
  | frame (dt : Float)
  | notes (st : TextInput)

structure Model where
  volume : Float := 0.4
  /-- The level meter, easing towards `volume`. -/
  meter : Tween := .at 0.4 (duration := 0.4) (easing := .outBack)
  options : Array Bool := #[true, false]
  name : TextInput := {}
  greeted : String := ""
  scroll : Nat := 0
  picked : Option Nat := none
  notes : TextInput := { text := "UVL draws everything in Lean: layout, text and pixels.\nTry Ctrl+arrows, double-click and Shift+Up." }

def update : Msg → Model → Model
  | .volume v, m => { m with volume := v, meter := m.meter.to v }
  | .toggle i, m => { m with options := m.options.modify i (!·) }
  | .name st, m => { m with name := st }
  | .submit, m => { m with greeted := m.name.text }
  | .scrolled o, m => { m with scroll := o }
  | .pick i, m => { m with picked := some i }
  | .frame dt, m => { m with meter := m.meter.step dt }
  | .notes st, m => { m with notes := st }

def items : List String :=
  (List.range 30).map fun i => s!"Item {i + 1}: " ++
    #["Lean", "WebGPU", "MSDF", "SDF", "Flexbox", "Elm"][i % 6]!

/-- A bar filled to `v ∈ [0, 1]` (it can overshoot slightly with `outBack`). -/
def meter (v : Float) : UI.Widget Msg :=
  canvas 220 10 fun r =>
    let fill := Max.max 0 (Min.min r.w (r.w * v))
    #[.fill (.roundedRect r (.all 5)) (Color.hex 0xE3E8EC),
      .fill (.roundedRect ⟨r.x, r.y, fill, r.h⟩ (.all 5))
        (.linear ⟨r.x, 0⟩ ⟨r.x + r.w, 0⟩ #[(0, Color.hex 0x43A047), (0.7, Color.hex 0xFDD835),
          (1, Color.hex 0xE53935)])]

def wordCount (s : String) : Nat :=
  ((s.split fun c => c == ' ' || c == '\n').filter (!·.isEmpty)).length

def view (m : Model) : UI.Widget Msg :=
  pad 20 <| row (gap := 20) (align := .start) [
    card <| col (gap := 14) [
      label "Controls" (size := 24) (color := Color.hex 0x0D47A1),
      row (gap := 10) [label "Volume" (size := 15), slider m.volume .volume (width := 180) (label := "Volume"),
        label s!"{(m.volume * 100).round.toUInt32}%" (size := 15)],
      row (gap := 10) [label "Level" (size := 15), meter m.meter.value],
      checkbox m.options[0]! (.toggle 0) "Dark grid lines" (size := 15),
      checkbox m.options[1]! (.toggle 1) "Show legend" (size := 15),
      textField "name" m.name .name (width := 260) (placeholder := "Type your name…")
        (onSubmit := some .submit),
      label (if m.greeted.isEmpty then "Press Enter to greet" else s!"Hello, {m.greeted}!")
        (size := 15) (color := Color.hex 0x546E7A)
    ],
    card (padding := 8) <| width 200 <| scrollView m.scroll .scrolled (height := 280) <|
      col (gap := 2) (align := .stretch) (items.zipIdx.map fun (s, i) =>
        onTap (.pick i) (radius := 6) <|
          decorated (fill := if m.picked.any (· == i) then some (.solid (Color.hex 0xBBDEFB)) else none)
            (radius := 6) (padXY 10 6 (label s (size := 14)))),
    card <| col (gap := 10) [
      label "Notes" (size := 18) (color := Color.hex 0x0D47A1),
      textArea "notes" m.notes .notes (width := 200) (lines := 9) (size := 15),
      label s!"{wordCount m.notes.text} words, {m.notes.text.length} characters" (size := 13)
        (color := Color.hex 0x546E7A)
    ]
  ]

def app : App Model Msg where
  init := {}
  update
  view
  subscriptions := fun e _ => match e with
    | .tick dt => some (.frame dt)
    | _ => none
  animating := fun m => !m.meter.done
  background := Color.hex 0xF5F7FA
  title := "uvl · controls"

end Examples.Controls
