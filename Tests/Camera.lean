import UVL

/-!
Camera and gesture tests: the world point under the fingers stays under the
fingers while panning and pinching, mouse drags and touches never pan twice,
and packed touch events decode.
-/

namespace Tests.Camera

open UVL Game

def check (name : String) (ok : Bool) : IO Bool := do
  IO.println s!"  [{if ok then "ok" else "FAIL"}] {name}"
  return ok

def near (a b : Float) : Bool := (a - b).abs < 1e-6
def nearV (a b : Vec2) : Bool := near a.x b.x && near a.y b.y

def feed (cam : Camera) (es : List Event) : Gestures × Camera :=
  es.foldl (fun (g, c) e => g.handle c e) ({}, cam)

def run : IO Bool := do
  let cam : Camera := { x := 100, y := 50, zoom := 2, maxZoom := 8 }
  let mut ok := true
  -- the affine transform and toScreen agree, and toWorld inverts them
  let p : Vec2 := ⟨130, 75⟩
  ok := (← check "toScreen = affine, toWorld inverts it"
    (nearV (cam.toScreen p) (cam.affine.apply p) && nearV (cam.toWorld (cam.toScreen p)) p)) && ok
  -- zoomAt keeps the world point under the focus
  let z := cam.zoomAt 1.5 200 120
  ok := (← check "zoomAt keeps the point under the focus"
    (near z.zoom 3 && nearV (z.toWorld ⟨200, 120⟩) (cam.toWorld ⟨200, 120⟩))) && ok
  ok := (← check "zoom is clamped" (near (cam.zoomAt 100 0 0).zoom cam.maxZoom)) && ok
  -- one finger drags the map: the world point under it follows it
  let w0 := cam.toWorld ⟨40, 40⟩
  let (g, c) := feed cam [.touchDown 7 40 40, .touchMove 7 55 30, .touchMove 7 70 90]
  ok := (← check "one finger pans" (nearV (c.toScreen w0) ⟨70, 90⟩ && g.active)) && ok
  -- two fingers: both world points stay under their fingers (pure scale + translate)
  let a0 := cam.toWorld ⟨100, 100⟩
  let b0 := cam.toWorld ⟨200, 100⟩
  let (_, c) := feed cam [.touchDown 1 100 100, .touchDown 2 200 100,
    .touchMove 2 300 100, .touchMove 1 50 100]
  ok := (← check "pinch keeps both fingers on their points"
    (nearV (c.toScreen a0) ⟨50, 100⟩ && nearV (c.toScreen b0) ⟨300, 100⟩ && near c.zoom 5)) && ok
  -- lifting a finger goes back to one-finger panning without a jump
  let (g, c2) := feed cam [.touchDown 1 100 100, .touchDown 2 200 100, .touchMove 2 300 100,
    .touchUp 1 100 100, .touchMove 2 310 100]
  let (_, c1) := feed cam [.touchDown 1 100 100, .touchDown 2 200 100, .touchMove 2 300 100]
  ok := (← check "after lifting a finger, the other one pans"
    (g.touches.size == 1 && near c2.zoom c1.zoom && near (c2.toScreen (c1.toWorld ⟨300, 100⟩)).x 310)) && ok
  -- the pointer the shell drives with the first finger does not pan again
  for order in [true, false] do
    let down : List Event := if order then [.pointerDown 10 10 .left, .touchDown 0 10 10]
      else [.touchDown 0 10 10, .pointerDown 10 10 .left]
    let (_, c) := feed cam (down ++ [.touchMove 0 30 10, .pointerMove 30 10])
    ok := (← check s!"emulated pointer ignored ({if order then "pointer" else "touch"} first)"
      (near c.x (cam.x - 20 / cam.zoom))) && ok
  -- mouse drag, wheel pan and Ctrl + wheel zoom around the pointer
  let (_, c) := feed cam [.pointerDown 10 10 .left, .pointerMove 20 30, .pointerUp 20 30 .left,
    .pointerMove 50 50]
  ok := (← check "mouse drag pans" (nearV ⟨c.x, c.y⟩ ⟨cam.x - 5, cam.y - 10⟩)) && ok
  let (_, c) := feed cam [.scroll 0 40]
  ok := (← check "wheel pans" (near c.y (cam.y + 20))) && ok
  let (_, c) := feed cam [.pointerMove 80 60, .keyDown .ctrl, .scroll 0 (-200)]
  ok := (← check "Ctrl + wheel zooms around the pointer"
    (c.zoom > cam.zoom && nearV (c.toWorld ⟨80, 60⟩) (cam.toWorld ⟨80, 60⟩))) && ok
  let (_, c) := feed cam [.pinch 0.5 10 20]
  ok := (← check "trackpad pinch zooms" (near c.zoom 1 && nearV (c.toWorld ⟨10, 20⟩) (cam.toWorld ⟨10, 20⟩))) && ok
  -- clamping to the world
  let c := ({ x := -50, y := 900, zoom := 1 } : Camera).clampTo 400 300 1000 1000
  ok := (← check "clampTo keeps the view inside the world" (near c.x 0 && near c.y 700)) && ok
  let c := ({ x := 0, y := 0, zoom := 0.25 } : Camera).clampTo 400 300 1000 1000
  ok := (← check "clampTo centers a small world" (near c.x (-300) && near c.y (-100))) && ok
  -- packed events from the shells
  let raw : FloatArray := ⟨#[13, 3, 10, 20, 0, 14, 3, 11, 21, 0, 15, 3, 12, 22, 0, 16, 1.25, 5, 6, 0]⟩
  let ok' := match (decodeEvents raw).toList with
    | [.touchDown 3 x0 y0, .touchMove 3 x1 y1, .touchUp 3 x2 y2, .pinch k x3 y3] =>
      x0 == 10 && y0 == 20 && x1 == 11 && y1 == 21 && x2 == 12 && y2 == 22 &&
        k == 1.25 && x3 == 5 && y3 == 6
    | _ => false
  ok := (← check "touch and pinch events decode" ok') && ok
  return ok

end Tests.Camera
