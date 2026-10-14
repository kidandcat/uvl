/-!
# Tweens and easing curves

A `Tween` animates one number towards a target over a fixed duration, shaped
by an `Easing` curve. Like all widget state it lives in the application's
model: the app subscribes to `tick` events while a tween runs and advances it.

```
structure Model where
  level : Tween := .at 0

def update : Msg → Model → Model
  | .setLevel v, m => { m with level := m.level.to v }
  | .frame dt, m => { m with level := m.level.step dt }

def app : App Model Msg where
  …
  subscriptions := fun e _ => match e with | .tick dt => some (.frame dt) | _ => none
  animating := fun m => !m.level.done
```

`to` starts from the value currently shown, so retargeting a running tween
(a slider dragged quickly) stays continuous.
-/

namespace UVL

inductive Easing where
  | linear
  | inQuad
  | outQuad
  | inOutQuad
  | inCubic
  | outCubic
  | inOutCubic
  /-- Overshoots slightly before settling. -/
  | outBack
  /-- A decaying oscillation around the target. -/
  | outElastic
deriving Inhabited, Repr, BEq

namespace Easing

/-- The curve at progress `t ∈ [0, 1]`; every curve maps 0 to 0 and 1 to 1. -/
def apply : Easing → Float → Float
  | .linear, t => t
  | .inQuad, t => t * t
  | .outQuad, t => t * (2 - t)
  | .inOutQuad, t => if t < 0.5 then 2 * t * t else 1 - 2 * (1 - t) * (1 - t)
  | .inCubic, t => t * t * t
  | .outCubic, t => 1 - (1 - t) ^ 3
  | .inOutCubic, t => if t < 0.5 then 4 * t * t * t else 1 - 4 * (1 - t) ^ 3
  | .outBack, t =>
    let c := 1.70158
    1 + (c + 1) * (t - 1) ^ 3 + c * (t - 1) ^ 2
  | .outElastic, t =>
    if t ≤ 0 then 0 else if t ≥ 1 then 1
    else 2 ^ (-10 * t) * Float.sin ((t * 10 - 0.75) * (2 * 3.141592653589793 / 3)) + 1

end Easing

/-- A number moving from `start` to `target` over `duration` seconds. -/
structure Tween where
  start : Float
  target : Float
  elapsed : Float := 0
  duration : Float := 0.25
  easing : Easing := .outCubic
deriving Inhabited, Repr

namespace Tween

/-- A tween resting at `v`. -/
def «at» (v : Float) (duration : Float := 0.25) (easing : Easing := .outCubic) : Tween :=
  { start := v, target := v, elapsed := duration, duration, easing }

/-- Progress in `[0, 1]`. -/
def progress (t : Tween) : Float :=
  if t.duration ≤ 0 then 1 else Min.min 1 (Max.max 0 (t.elapsed / t.duration))

def done (t : Tween) : Bool := t.progress ≥ 1

/-- The value to show now. -/
def value (t : Tween) : Float :=
  if t.done then t.target else t.start + (t.target - t.start) * t.easing.apply t.progress

/-- Head for `v`, starting from the current value (no-op if `v` is already the
target). -/
def to (t : Tween) (v : Float) : Tween :=
  if v == t.target then t else { t with start := t.value, target := v, elapsed := 0 }

/-- Advance by `dt` seconds. -/
def step (t : Tween) (dt : Float) : Tween :=
  if t.done then t else { t with elapsed := t.elapsed + dt }

end Tween

end UVL
