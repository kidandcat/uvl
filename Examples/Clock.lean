import UVL

/-! A stopwatch that runs by itself: it only listens to `tick` events, so it
needs no input at all (bare-metal panels without touch or buttons). -/

namespace Examples.Clock
open UVL UI

inductive Msg where
  | tick (dt : Float)

structure Model where
  /-- Milliseconds since start. -/
  ms : Nat := 0
deriving Repr

def update : Msg → Model → Model
  | .tick dt, m => { ms := m.ms + (dt * 1000).round.toUInt64.toNat }

def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

/-- `mm:ss`, or `h:mm:ss` from the first hour on. -/
def format (ms : Nat) : String :=
  let s := ms / 1000
  let (h, m, s) := (s / 3600, s / 60 % 60, s % 60)
  if h == 0 then s!"{pad2 m}:{pad2 s}" else s!"{h}:{pad2 m}:{pad2 s}"

def view (m : Model) : UI.Widget Msg := ui! center:
  col (gap := 4) (align := .center):
    text "uptime" (size := 2) (color := Color.hex 0x90A4AE)
    -- one size smaller once the hours appear, so `h:mm:ss` fits 240 px
    text (format m.ms) (size := if m.ms < 3600000 then 6 else 5) (color := Color.white)

def app : App Model Msg where
  init := {}
  update
  view
  subscriptions
    | .tick dt, _ => some (.tick dt)
    | _, _ => none
  background := Color.hex 0x102027
  title := "uvl · clock"

end Examples.Clock
