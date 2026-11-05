# Verified animation

`UVL.Anim` models an animation as a pure function of elapsed time. There is no
accumulator that adds `dt` into a running total inside the proved core, so a
dropped frame is just a larger elapsed time.

Time and values in `UVL/Anim/Basic.lean` and `UVL/Anim/Group.lean` are `Rat`.
No proof uses `sorry`, and the files add no axiom. `lake build` / `lake test`
typecheck the proofs because `UVL.lean` imports the modules.

The float `Tween` in `UVL/UI/Tween.lean` is a different API. It is covered by
the controls tests, not by these theorems.

## What a clip is

```text
progress(duration, elapsed) =
  1                          if duration ≤ 0
  clamp01(elapsed / duration) otherwise

sample = start + (target - start) * ease(progress)
```

`clamp01` sends everything outside `[0, 1]` to the nearer endpoint. A
non-positive duration is already finished: the sample is `target` at every
time, including negative times.

Easings are polynomials. `outBack` uses overshoot constant `17/10` (the usual
`1.70158` is not rational). A sine elastic is not here; it stays on `Tween`.

`Easing.IsMonotone` is true for every easing except `outBack`.

## Theorems

### Endpoints, for every easing

| Theorem | Guarantee |
| --- | --- |
| `Easing.apply_zero` | `ease(0) = 0` |
| `Easing.apply_one` | `ease(1) = 1` |
| `sample_le_zero`, `Clip.sample_le_zero` | If `duration > 0` and `elapsed ≤ 0`, the value is `start` |
| `sample_ge_duration`, `Clip.sample_ge_duration` | If `elapsed ≥ duration`, the value is `target` |
| `sample_nonpos_duration`, `Clip.sample_nonpos_duration` | If `duration ≤ 0`, the value is `target` at every time |
| `Clip.retarget_continuous` | Retargeting with a positive duration does not jump: local time `0` is the value at the interruption |
| `Clip.retarget_ge_duration` | After the new duration, the value is the new target |
| `Clip.reverse_continuous` | Reversal is a retarget back to `start`, continuous at the turn |
| `Clip.reverse_ge_duration` | A reversal ends exactly at the original `start` |
| `Easing.outBack_exceeds_one` | `outBack(7/10) > 1`. The range claim does not include it |

`sample_ge_duration` is also the no-overshoot fact: a single step with
`dt ≥ duration` lands on `target`, not past it.

### The value stays in range

| Theorem | Guarantee |
| --- | --- |
| `Easing.apply_unitInterval` | A monotone easing sends `[0, 1]` into `[0, 1]` |
| `Easing.apply_monotone` | On `[0, 1]`, a monotone easing preserves order |
| `sample_between`, `Clip.sample_between` | The sample lies between `start` and `target`, in either order |
| `Clip.cancelValue_snap` | Snap-to-end is the target |
| `Clip.cancelValue_hold` | Hold is the current sample |
| `Clip.cancelValue_between` | For a monotone easing, both policies land inside start–target |
| `Clip.freeze_const` | A frozen clip is that value at every later time |
| `Clip.cancel_stable` | The clip produced by cancelling keeps the cancelled value forever |

### Same clock, groups

| Theorem | Guarantee |
| --- | --- |
| `Clip.same_duration_sync` | Two clips with the same duration, sampled at the same elapsed time past that duration, are each exactly at their own target |
| `Group.parallel_sync` | A non-empty parallel group whose clips share duration `d ≥ 0` has duration `d`, and every clip is at its target from then on |
| `parallel_duration`, `Group.parallel_duration` | Parallel duration is the max of the clip durations (and at least `0`) |
| `sequence_duration`, `Group.sequence_duration` | If every duration is `≥ 0`, a sequence lasts the sum |
| `sequence_join` | At the first clip's duration it is at its target, and the next clip (positive duration) is still at its start |
| `staggerDuration_succ` | For `n > 0`, the closed form is `(n - 1) * delay + d` |
| `stagger_uniform`, `Group.stagger_uniform` | Equal durations `d ≥ 0` and delay `≥ 0`: the stagger lasts `staggerDuration` |
| `Span.sample_ge_finish` | A member at or after `offset + duration` is at its target |
| `spans_done`, `Group.done` | At the group's computed duration, every member is at its target |
| `Span.reverse_continuous`, `Span.reverse_ge_duration` | Reversing one member on the same group clock holds the current value, then ends at that clip's start |

Empty groups have duration `0` and no members. `Group.done` does not need
durations to be positive: the duration it uses is the actual latest finish.

### Frame independence

| Theorem | Guarantee |
| --- | --- |
| `foldl_add_eq_sum` | Adding the deltas in order equals the list sum |
| `stepped_eq_sample`, `Clip.stepped_eq_sample` | Sampling after those additions equals sampling the sum |
| `schedules_agree`, `Clip.schedules_agree` | Two lists of deltas with the same sum produce the same value |
| `stepped_past_end`, `Clip.stepped_past_end` | The list `[dt]` with `dt ≥ duration` is exactly the target |
| `Clock.after_sum` | Advancing a clock by a list of deltas moves it by their sum |
| `Clock.playing_frame_independent` | A clip played on that clock agrees for any two schedules with the same sum |

Nothing in these statements clamps per frame. A coarse schedule and a fine one
meet whenever the sums meet.

## Pixels, and what is not proved

`toPixel x = floor(x + 1/2)` (halves toward `+∞`).

| Theorem | Guarantee |
| --- | --- |
| `toPixel_intCast` | `toPixel` of an integer rational is that integer |
| `Clip.toPixel_at_end` | The pixel of a finished sample is the pixel of the exact target |
| `Clip.toPixel_at_end_int` | If that target is an integer `n`, the pixel is `n` |
| `toUnitByte_zero`, `toUnitByte_one` | Opacity `0` and `1` are bytes `0` and `255` |
| `Clip.toUnitByte_at_end` | A finished opacity byte is the byte of the exact target |

`UI.shift` pads by `natOfPixel` (`Int.toNat`, so negatives become `0`). The
child's layout rectangle is that integer. The demo test checks the motion box
is at `(280, 48)` when the target is `280`, and that the rasterizer's center
pixel is the blue used for the box.

`millisOfFloat` rounds a `Float` tick to a millisecond and clamps non-positive
`dt` to `0`. It is not proved. Dyadic seconds used by the runtime test (`0.25`,
`0.5`, `0.75`, `1`) happen to be exact in binary floating point; the test
checks that `1` and `0.25 + 0.75` both become `1000` ms and the same pixel.
Two different `Float` sequences that round to different millisecond totals are
different clocks. The proof starts after that rounding.

`UI.withByteAlpha` stores byte `n` as the float `n / 255` in `Color.a`.
`Color.toByte` rounding that float back is not a theorem (`Float` is opaque).
The demo test checks the endpoints the rasterizer actually writes: alpha `0`
leaves the background, alpha `255` writes the solid red.

`Nat.toF` of a pixel below `2^30` is the library's integer-to-float cast
(`UVL.Core.FloatLit`). That the resulting `Float` equals the real number is
IEEE-754, not a Lean equality. The proved object is the integer the layout
uses.

## What the tests cover besides the proofs

`Tests/Anim.lean` (`lake test`) drives `Examples/Anim.lean`:

* start pixel `24` and alpha byte `0`; at `800` ms, pixel `280` and byte `255`
* the sequence hand-off at `4/15` and the stagger finishing with the same `4/5`
* `100+150+50+500` ms equals one `800` ms step
* retarget to `100`, reverse back to the starts, snap, and hold
* the laid-out box is the proved pixel, and the painted centers match
* runtime ticks `1` and `0.25+0.75`, and a real click on Reverse

`lake exe uvl-demo` writes `out/anim-start.png`, `out/anim-mid.png`,
`out/anim-end.png` and `out/anim-reverse.png`. The settled frame is
`Tests/golden/anim.png`.
