import UVL

/-! A phone-sized example (portrait, touch first): a counter with its history
chart, a slider driving an animated level meter, toggles and a text field.
It is the app of the Android build (`android/build.sh`), and runs anywhere
else UVL does. -/

namespace Examples.Phone
open UVL UI

inductive Msg where
  | inc
  | dec
  | reset
  | volume (v : Float)
  | toggle (i : Nat)
  | name (st : TextInput)
  | submit
  | frame (dt : Float)

structure Model where
  count : Int := 7
  history : List Int := [0, 2, 1, 4, 3, 6, 5, 7]
  volume : Float := 0.4
  /-- The level meter, easing towards `volume`. -/
  meter : Tween := .at 0.4 (duration := 0.4) (easing := .outBack)
  /-- Smooth chart, show the second series. -/
  options : Array Bool := #[true, false]
  name : TextInput := {}
  greeted : String := ""

def record (m : Model) (v : Int) : Model :=
  let h := m.history ++ [v]
  { m with count := v, history := h.drop (h.length - 16) }

def update : Msg → Model → Model
  | .inc, m => record m (m.count + 1)
  | .dec, m => record m (m.count - 1)
  | .reset, m => { m with count := 0, history := [0] }
  | .volume v, m => { m with volume := v, meter := m.meter.to v }
  | .toggle i, m => { m with options := m.options.modify i (!·) }
  | .name st, m => { m with name := st }
  | .submit, m => { m with greeted := m.name.text }
  | .frame dt, m => { m with meter := m.meter.step dt }

def accent : Color := Color.hex 0x0D47A1
def muted : Color := Color.hex 0x546E7A

/-- A bar filled to `v ∈ [0, 1]` (it can overshoot slightly with `outBack`). -/
def meter (v : Float) : UI.Widget Msg :=
  canvas 200 10 fun r =>
    let fill := Max.max 0 (Min.min r.w (r.w * v))
    #[.fill (.roundedRect r (.all 5)) (Color.hex 0xE3E8EC),
      .fill (.roundedRect ⟨r.x, r.y, fill, r.h⟩ (.all 5))
        (.linear ⟨r.x, 0⟩ ⟨r.x + r.w, 0⟩ #[(0, Color.hex 0x43A047), (0.7, Color.hex 0xFDD835),
          (1, Color.hex 0xE53935)])]

/-- Moving average over three points, for the "smooth" option. -/
def smooth (xs : List Float) : List Float :=
  let a := xs.toArray
  (List.range a.size).map fun i =>
    let lo := if i == 0 then 0 else i - 1
    let hi := Min.min (a.size - 1) (i + 1)
    let s := (List.range (hi + 1 - lo)).foldl (fun acc k => acc + a[lo + k]!) 0
    s / (hi + 1 - lo).toFloat

def series (m : Model) : List (List Float) :=
  let raw := m.history.map fun v => (v + 16).toNat.toFloat
  let main := if m.options[0]! then smooth raw else raw
  if m.options[1]! then [main, raw.map (fun v => v * m.volume)] else [main]

def view (m : Model) : UI.Widget Msg :=
  pad 16 <| col (gap := 14) (align := .stretch) [
    row (gap := 10) [
      label "UVL" (size := 28) (color := accent),
      label "on Android" (size := 18) (color := muted),
      spacer,
      chip "Lean 4"
    ],
    card <| row (gap := 16) (justify := .center) [
      button "-" (size := 4) (color := Color.hex 0xE53935) (onTap := some .dec),
      width 120 <| row (justify := .center) [label (toString m.count) (size := 44)],
      button "+" (size := 4) (color := Color.hex 0x43A047) (onTap := some .inc)
    ],
    expanded <| card <| col (gap := 8) (align := .stretch) [
      row [
        label "History" (size := 16),
        spacer,
        button "Reset" (size := 1) (color := Color.gray) (onTap := some .reset)
      ],
      expanded <| lineChart (series m)
    ],
    card <| col (gap := 12) [
      row (gap := 10) [label "Level" (size := 15), slider m.volume .volume (width := 170),
        label s!"{(m.volume * 100).round.toUInt32}%" (size := 15)],
      meter m.meter.value,
      checkbox m.options[0]! (.toggle 0) "Smooth the chart" (size := 15),
      checkbox m.options[1]! (.toggle 1) "Show the scaled series" (size := 15),
      textField "name" m.name .name (width := 260) (placeholder := "Type your name…")
        (onSubmit := some .submit),
      label (if m.greeted.isEmpty then "Tap the field and press Enter" else s!"Hello, {m.greeted}!")
        (size := 15) (color := muted)
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
  title := "uvl · phone"

end Examples.Phone
