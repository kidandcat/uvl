import UVL

/-! Interactive example: a counter with a history chart (Elm architecture). -/

namespace Examples.Counter
open UVL UI

inductive Msg where
  | inc
  | dec
  | reset
deriving BEq, Repr, Inhabited

structure Model where
  count : Int := 0
  history : List Int := [0]
deriving Repr

def record (m : Model) (v : Int) : Model :=
  let h := m.history ++ [v]
  { count := v, history := h.drop (h.length - 12) }

def update : Msg → Model → Model
  | .inc, m => record m (m.count + 1)
  | .dec, m => record m (m.count - 1)
  | .reset, _ => {}

def view (m : Model) : UI.Widget Msg := ui! pad 24:
  col (gap := 16) (align := .stretch):
    row (gap := 12):
      text "Counter" (size := 3) (color := Color.hex 0x0D47A1)
      spacer
      chip "+/- or arrows"
    card:
      row (gap := 16) (justify := .center):
        button "-" (size := 4) (color := Color.red) (onTap := some Msg.dec)
        width 160: row (justify := .center): text (toString m.count) (size := 6)
        button "+" (size := 4) (color := Color.green) (onTap := some Msg.inc)
    expanded:
      card:
        col (gap := 8) (align := .stretch):
          row:
            text "History"
            spacer
            button "Reset" (size := 1) (color := Color.gray) (onTap := some Msg.reset)
          expanded:
            lineChart [m.history.map fun v => (v + 12).toNat.toF]

def app : App Model Msg where
  init := {}
  update
  view
  subscriptions
    | .keyDown (.char '+'), _ | .keyDown .up, _ | .keyDown .right, _ => some .inc
    | .keyDown (.char '-'), _ | .keyDown .down, _ | .keyDown .left, _ => some .dec
    | .keyDown (.char 'r'), _ => some .reset
    | _, _ => none
  background := Color.hex 0xF5F7FA
  title := "uvl · counter"

end Examples.Counter
