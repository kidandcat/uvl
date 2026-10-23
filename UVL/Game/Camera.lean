import UVL.Core.Geometry
import UVL.App.Event

/-!
# 2D camera and pan/zoom gestures

A `Camera` maps world coordinates (map units, e.g. pixels of a tile map at
zoom 1) to screen pixels with a uniform zoom. `Gestures` turns raw input into
camera moves, the way map and strategy games on phones do:

* one finger (or the left mouse button) drags the map;
* two fingers pinch to zoom around their midpoint and pan as the midpoint moves;
* the wheel (two-finger trackpad scroll) pans, Ctrl/Cmd + wheel and the
  trackpad pinch zoom around the pointer.

Everything is pure: an app keeps a `Camera` and a `Gestures` in its model and
feeds them the events it receives through `App.subscriptions`.
-/

namespace UVL.Game

structure Camera where
  /-- World point shown at the top-left corner of the viewport. -/
  x : Float := 0
  y : Float := 0
  /-- Screen pixels per world unit. -/
  zoom : Float := 1
  minZoom : Float := 0.25
  maxZoom : Float := 4
deriving Inhabited, Repr, BEq

namespace Camera

def toScreen (c : Camera) (p : Vec2) : Vec2 := ⟨(p.x - c.x) * c.zoom, (p.y - c.y) * c.zoom⟩

def toWorld (c : Camera) (p : Vec2) : Vec2 := ⟨p.x / c.zoom + c.x, p.y / c.zoom + c.y⟩

/-- World → screen as an affine transform (for `RenderOp.transform`). -/
def affine (c : Camera) : Affine :=
  { a := c.zoom, d := c.zoom, e := -c.x * c.zoom, f := -c.y * c.zoom }

/-- The world rectangle visible in a `vw × vh` viewport. -/
def visible (c : Camera) (vw vh : Float) : Rect := ⟨c.x, c.y, vw / c.zoom, vh / c.zoom⟩

/-- Move the content by a screen-space delta (the map follows the finger). -/
def pan (c : Camera) (dx dy : Float) : Camera :=
  { c with x := c.x - dx / c.zoom, y := c.y - dy / c.zoom }

/-- Multiply the zoom by `k` (clamped to `[minZoom, maxZoom]`), keeping the
world point under screen point `(sx, sy)` in place. -/
def zoomAt (c : Camera) (k sx sy : Float) : Camera :=
  let z := Max.max c.minZoom (Min.min c.maxZoom (c.zoom * k))
  let w := c.toWorld ⟨sx, sy⟩
  { c with zoom := z, x := w.x - sx / z, y := w.y - sy / z }

/-- Keep a `vw × vh` viewport inside a `bw × bh` world; along an axis where the
world is smaller than the viewport, center it. -/
def clampTo (c : Camera) (vw vh bw bh : Float) : Camera :=
  let fit (v world view : Float) : Float :=
    let span := view / c.zoom
    if span >= world then (world - span) / 2 else Max.max 0 (Min.min v (world - span))
  { c with x := fit c.x bw vw, y := fit c.y bh vh }

end Camera

/-- Input state for camera gestures. -/
structure Gestures where
  /-- Fingers on the screen: id and last position, in touch order. -/
  touches : Array (Nat × Vec2) := #[]
  /-- Last position of a mouse drag in progress. -/
  drag : Option Vec2 := none
  /-- Last pointer position (where Ctrl + wheel zooms). -/
  pointer : Vec2 := ⟨0, 0⟩
  /-- Ctrl (or Cmd) held. -/
  ctrl : Bool := false
deriving Inhabited, Repr

namespace Gestures

/-- Zoom factor per pixel of Ctrl + wheel scroll. -/
def wheelZoomRate : Float := 1 / 200

/-- Midpoint and distance of the first two fingers. -/
def pair (ts : Array (Nat × Vec2)) : Option (Vec2 × Float) :=
  match ts[0]?, ts[1]? with
  | some (_, a), some (_, b) => some (Vec2.lerp a b 0.5, (b - a).length)
  | _, _ => none

/-- Feed one event, updating the gesture state and the camera.

Shells also drive the pointer with the first finger, in either order relative
to the touch events; mouse drags are ignored while fingers are down, and a new
finger cancels a mouse drag, so a finger never pans twice. -/
def handle (g : Gestures) (cam : Camera) (e : Event) : Gestures × Camera :=
  match e with
  | .touchDown id x y =>
    ({ g with touches := (g.touches.filter (·.1 != id)).push (id, ⟨x, y⟩), drag := none }, cam)
  | .touchMove id x y =>
    match g.touches.findIdx? (·.1 == id) with
    | none => (g, cam)
    | some i =>
      let p : Vec2 := ⟨x, y⟩
      let ts := g.touches.set! i (id, p)
      let g' := { g with touches := ts }
      if i ≥ 2 then (g', cam)
      else match pair g.touches, pair ts with
        | some (m0, d0), some (m1, d1) =>
          let k := if d0 > 1 && d1 > 1 then d1 / d0 else 1
          (g', (cam.zoomAt k m0.x m0.y).pan (m1.x - m0.x) (m1.y - m0.y))
        | _, _ =>
          let q := g.touches[i]!.2
          (g', cam.pan (p.x - q.x) (p.y - q.y))
  | .touchUp id _ _ => ({ g with touches := g.touches.filter (·.1 != id) }, cam)
  | .pointerDown x y .left =>
    ({ g with pointer := ⟨x, y⟩, drag := if g.touches.isEmpty then some ⟨x, y⟩ else none }, cam)
  | .pointerMove x y =>
    let g' := { g with pointer := ⟨x, y⟩ }
    match g.drag with
    | some q =>
      if g.touches.isEmpty then ({ g' with drag := some ⟨x, y⟩ }, cam.pan (x - q.x) (y - q.y))
      else ({ g' with drag := none }, cam)
    | none => (g', cam)
  | .pointerUp x y .left => ({ g with pointer := ⟨x, y⟩, drag := none }, cam)
  | .scroll dx dy =>
    if g.ctrl then (g, cam.zoomAt (Float.exp (-dy * wheelZoomRate)) g.pointer.x g.pointer.y)
    else (g, cam.pan (-dx) (-dy))
  | .pinch k x y => (g, cam.zoomAt k x y)
  | .keyDown .ctrl => ({ g with ctrl := true }, cam)
  | .keyUp .ctrl => ({ g with ctrl := false }, cam)
  | _ => (g, cam)

/-- Is the camera being moved by a finger or a mouse drag? -/
def active (g : Gestures) : Bool := !g.touches.isEmpty || g.drag.isSome

end Gestures

end UVL.Game
