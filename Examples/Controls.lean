import UVL

/-! Interactive example: stateful controls (slider, checkboxes, text field and
a scroll view), with all their state in the model (Elm architecture). -/

namespace Examples.Controls
open UVL UI

inductive Msg where
  | volume (v : Float)
  | toggle (i : Nat)
  | name (st : TextInput)
  | submit
  | scrolled (offset : Nat)
  | pick (i : Nat)

structure Model where
  volume : Float := 0.4
  options : Array Bool := #[true, false]
  name : TextInput := {}
  greeted : String := ""
  scroll : Nat := 0
  picked : Option Nat := none

def update : Msg → Model → Model
  | .volume v, m => { m with volume := v }
  | .toggle i, m => { m with options := m.options.modify i (!·) }
  | .name st, m => { m with name := st }
  | .submit, m => { m with greeted := m.name.text }
  | .scrolled o, m => { m with scroll := o }
  | .pick i, m => { m with picked := some i }

def items : List String :=
  (List.range 30).map fun i => s!"Item {i + 1}: " ++
    #["Lean", "WebGPU", "MSDF", "SDF", "Flexbox", "Elm"][i % 6]!

def view (m : Model) : UI.Widget Msg :=
  pad 20 <| row (gap := 20) (align := .start) [
    card <| col (gap := 14) [
      label "Controls" (size := 24) (color := Color.hex 0x0D47A1),
      row (gap := 10) [label "Volume" (size := 15), slider m.volume .volume (width := 180),
        label s!"{(m.volume * 100).round.toUInt32}%" (size := 15)],
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
            (radius := 6) (padXY 10 6 (label s (size := 14))))
  ]

def app : App Model Msg where
  init := {}
  update
  view
  background := Color.hex 0xF5F7FA
  title := "uvl · controls"

end Examples.Controls
