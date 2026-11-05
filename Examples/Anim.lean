import UVL

/-!
Verified animation, driven as `value = f(t)` on a millisecond clock.

The motion, the fade, a three-leg sequence and a three-bar stagger are all
built to finish at 800 ms. Reverse and retarget restart from the sample at
that instant; snap and hold are the two cancel policies.
-/

namespace Examples.Anim

open UVL UI Anim

def motion0 : Clip := { start := 24, target := 280, duration := 4 / 5, easing := .outCubic }
def fade0 : Clip := { start := 0, target := 1, duration := 4 / 5, easing := .inOutQuad }

def leg (a b : Rat) : Clip :=
  { start := a, target := b, duration := 4 / 15, easing := .inOutCubic }

/-- Three legs, total `3 * 4/15 = 4/5`. -/
def route0 : List Span := sequence [leg 24 120, leg 120 200, leg 200 280]

def barClip : Clip := { start := 8, target := 36, duration := 2 / 5, easing := .smoothstep }

/-- Delay `1/5`, three equal clips: `(3 - 1) * (1/5) + 2/5 = 4/5`. -/
def bars0 : List Span := stagger (1 / 5) [barClip, barClip, barClip]

inductive Msg where
  | advance (ms : Int)
  | tick (dt : Float)
  | reverse
  | retarget
  | snap
  | hold
  | replay
deriving Inhabited, BEq

structure Model where
  ms : Int := 0
  motion : Clip := motion0
  motionOrigin : Int := 0
  fade : Clip := fade0
  route : List Span := route0
  bars : List Span := bars0
  groupOrigin : Int := 0
  note : String := "playing"
deriving Inhabited

def now (m : Model) : Rat := (m.ms : Rat) / 1000

def since (ms origin : Int) : Rat := ((ms - origin : Int) : Rat) / 1000

def motionElapsed (m : Model) : Rat := since m.ms m.motionOrigin

def groupElapsed (m : Model) : Rat := since m.ms m.groupOrigin

/-- Restart every span from its sample at `t`, on a clock that is about to be zeroed. -/
def restartReverse (s : Span) (t : Rat) : Span where
  offset := 0
  clip := s.clip.reverse (t - s.offset)

def advanceMs (m : Model) (dt : Int) : Model := { m with ms := m.ms + dt }

def update : Msg → Model → Model
  | .advance n, m => advanceMs m n
  | .tick dt, m => advanceMs m (millisOfFloat dt)
  | .reverse, m =>
    let t := groupElapsed m
    { m with
      motion := m.motion.reverse (motionElapsed m)
      motionOrigin := m.ms
      route := m.route.map (restartReverse · t)
      bars := m.bars.map (restartReverse · t)
      groupOrigin := m.ms
      note := "reverse" }
  | .retarget, m =>
    { m with
      motion := m.motion.retarget (motionElapsed m) 100 m.motion.duration
      motionOrigin := m.ms
      note := "retarget" }
  | .snap, m =>
    { m with
      motion := m.motion.cancel (motionElapsed m) .snapToEnd
      motionOrigin := m.ms
      note := "snap" }
  | .hold, m =>
    { m with
      motion := m.motion.cancel (motionElapsed m) .hold
      motionOrigin := m.ms
      note := "hold" }
  | .replay, _ => {}

def motionPixel (m : Model) : Int := toPixel (m.motion.sample (motionElapsed m))

def fadeByte (m : Model) : Int := toUnitByte (m.fade.sample (since m.ms 0))

def spanPixel (s : Span) (t : Rat) : Int := toPixel (s.sample t)

/-- The value a sequence shows: the latest leg that has started, which is the
last leg's target once the whole sequence is done. -/
def shown (spans : List Span) (t : Rat) : Rat :=
  spans.foldl (fun acc s => if decide (t < s.offset) then acc else s.sample t) 0

def running (c : Clip) (elapsed : Rat) : Bool :=
  decide (elapsed < c.duration) && decide (0 < c.duration)

def anyRunning (spans : List Span) (t : Rat) : Bool :=
  spans.any fun s => running s.clip (t - s.offset)

def view (m : Model) : UI.Widget Msg :=
  let gt := groupElapsed m
  let marker := toPixel (shown m.route gt)
  let bars := m.bars.zipIdx.map fun (s, i) =>
    let h := natOfPixel (spanPixel s gt)
    shift (24 + (i : Int) * 48) (210 + (36 - (h : Int))) (box (18 + i * 4) h (Color.hex 0x00897B))
  stack ([
    col (gap := 6) [
      row [text "Animation" (size := 2) (color := Color.hex 0x0D47A1), spacer,
        text m.note (size := 1)],
      text s!"x {motionPixel m}  a {fadeByte m}" (size := 1) (color := Color.hex 0x546E7A)],
    shift 16 268 <| row [
      button "Reverse" (onTap := some .reverse) (size := 1),
      button "Retarget" (onTap := some .retarget) (size := 1),
      button "Snap" (onTap := some .snap) (size := 1),
      button "Hold" (onTap := some .hold) (size := 1),
      button "Replay" (onTap := some .replay) (size := 1)],
    shift (motionPixel m) 48 (box 37 29 Color.blue),
    shift 24 96 (box 41 41 (withByteAlpha Color.red (fadeByte m))),
    shift marker 156 (box 16 16 (Color.hex 0xFB8C00))
  ] ++ bars)

def app : App Model Msg where
  init := {}
  update := update
  view := view
  subscriptions := fun e _ => match e with
    | .tick dt => some (.tick dt)
    | _ => none
  animating := fun m =>
    running m.motion (motionElapsed m) || running m.fade (since m.ms 0) ||
      anyRunning m.route (groupElapsed m) || anyRunning m.bars (groupElapsed m)
  background := Color.hex 0xF5F7FA
  title := "uvl · animation"

def atMs (n : Int) : Model := update (.advance n) {}

def stageW : Nat := 480
def stageH : Nat := 320

def renderAt (m : Model) : FrameBuffer stageW stageH :=
  UI.render (view m) stageW stageH (Color.hex 0xF5F7FA)

def reversed : Model := update (.advance 800) (update .reverse (atMs 400))

end Examples.Anim
