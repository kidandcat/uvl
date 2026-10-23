import UVL

/-!
# Sprites: a strategy-game map

A 64 × 64 tile map with units walking around it, a camera that pans and zooms
(mouse drag, wheel, Ctrl + wheel and trackpad pinch on desktop; one- and
two-finger gestures on touch screens) and an fps counter. Everything is drawn
from one generated texture atlas, as two `RenderOp.sprites` batches: the
visible terrain tiles, then the visible units sorted by depth.
-/

namespace Examples.Sprites
open UVL UI Game

/-- Tile size in world units (and texels). -/
def tileSize : Nat := 32
def mapSize : Nat := 64
def worldSize : Float := (tileSize * mapSize).toFloat

/-! ## Texture atlas

256 × 64 texels: the first row holds eight terrain tiles, the second four unit
colors with two walking frames each. -/

def atlasW : Nat := 256
def atlasH : Nat := 64

/-- A deterministic hash of three small numbers to `[0, 1)`. -/
def hash (x y s : Nat) : Float :=
  let v : UInt64 := (x.toUInt64 * 73856093) ^^^ (y.toUInt64 * 19349663) ^^^ (s.toUInt64 * 83492791)
  let v := v * 0x9E3779B97F4A7C15
  let v := v ^^^ (v >>> 29)
  (v &&& 0xFFFF).toFloat / 65536

@[inline] def clamp01 (v : Float) : Float := Max.max 0 (Min.min 1 v)

/-- Coverage of a disc of radius `r` centered at `(cx, cy)` at texel `(x, y)`. -/
def disc (x y : Nat) (cx cy r : Float) : Float :=
  let dx := x.toFloat + 0.5 - cx
  let dy := y.toFloat + 0.5 - cy
  clamp01 (r - Float.sqrt (dx * dx + dy * dy) + 0.5)

def mix (a b : Color) (t : Float) : Color := Color.lerp a b (clamp01 t)

def grass (x y k : Nat) : Color :=
  mix (Color.rgb 0.29 0.55 0.24) (Color.rgb 0.35 0.62 0.27) (hash x y k)

/-- Terrain tile `k` at texel `(x, y)` of the tile. -/
def terrainTexel (k x y : Nat) : Color :=
  match k with
  | 0 => grass x y 0
  | 1 =>
    let flower := disc x y 9 11 1.6 + disc x y 22 20 1.6 + disc x y 14 26 1.4
    mix (grass x y 1) (Color.rgb 0.95 0.85 0.3) flower
  | 2 => mix (Color.rgb 0.82 0.74 0.5) (Color.rgb 0.88 0.8 0.56) (hash x y 2)
  | 3 | 4 =>
    let wave := Float.sin ((x.toFloat + 2 * y.toFloat + (if k == 4 then 8 else 0)) * 0.39)
    mix (Color.rgb 0.17 0.38 0.72) (Color.rgb 0.3 0.52 0.85) (wave * 0.5 + 0.5 - 0.4 * hash x y 3)
  | 5 =>
    let trunk := if x ≥ 14 && x < 18 && y ≥ 20 && y < 29 then 1 else 0
    let crown := disc x y 16 14 10
    let g := mix (grass x y 5) (Color.rgb 0.4 0.26 0.13) trunk
    mix g (mix (Color.rgb 0.1 0.36 0.14) (Color.rgb 0.16 0.45 0.18) (hash x y 5)) crown
  | 6 => mix (Color.rgb 0.5 0.5 0.53) (Color.rgb 0.6 0.6 0.62) (hash (x / 4) (y / 4) 6)
  | _ =>
    let rock := disc x y 17 18 8
    mix (grass x y 7) (mix (Color.rgb 0.45 0.45 0.48) (Color.rgb 0.62 0.62 0.65) (1 - y.toFloat / 28)) rock

def teamColors : Array Color :=
  #[Color.hex 0xE53935, Color.hex 0x1E88E5, Color.hex 0xFDD835, Color.hex 0x8E24AA]

/-- Unit of team `c` in walking frame `f` at texel `(x, y)` (transparent around it). -/
def unitTexel (c f x y : Nat) : Color :=
  let team := teamColors[c]!
  let dark := Color.lerp team Color.black 0.45
  let skin := Color.rgb 0.96 0.8 0.64
  -- legs swap between the two frames
  let (l1, l2) := if f == 0 then (12, 18) else (14, 16)
  let legs := if y ≥ 22 && y < 30 && ((x ≥ l1 && x < l1 + 3) || (x ≥ l2 && x < l2 + 3)) then 1.0 else 0
  let shadow := 0.35 * clamp01 (1 - ((x.toFloat + 0.5 - 16) / 10) ^ 2 - ((y.toFloat + 0.5 - 30) / 2.5) ^ 2)
  let body := disc x y 16 17 7
  let outline := disc x y 16 17 8
  let head := disc x y 16 8 4.5
  let headOutline := disc x y 16 8 5.5
  let a := Max.max (Max.max shadow legs) (Max.max outline headOutline)
  if a <= 0 then Color.transparent else
  let col := if legs > 0 then dark else if shadow > outline && shadow > headOutline then Color.black
    else mix (mix dark team body) (mix Color.black skin head) (if head > 0 then 1 else 0)
  { col with a := a }

def atlasPixel (x y : Nat) : Color :=
  if y < tileSize then terrainTexel (x / tileSize) (x % tileSize) y
  else
    let k := x / tileSize
    unitTexel (k / 2) (k % 2) (x % tileSize) (y - tileSize)

def toByte (v : Float) : UInt8 := (clamp01 v * 255).round.toUInt8

/-- The atlas. Textures are identified by `id` (`Texture`), so it must differ
from every other texture of the process (`Examples.spriteSheet` is 1). -/
def atlas : Texture := Id.run do
  let mut px := ByteArray.emptyWithCapacity (atlasW * atlasH * 4)
  for y in [0:atlasH] do
    for x in [0:atlasW] do
      let c := atlasPixel x y
      px := px.push (toByte c.r) |>.push (toByte c.g) |>.push (toByte c.b) |>.push (toByte c.a)
  return { id := 2, w := atlasW, h := atlasH, pixels := px }

/-! ## Map -/

/-- Smooth value noise in `[0, 1)` with cells of `cell` tiles. -/
def noise (x y cell s : Nat) : Float :=
  let fx := x.toFloat / cell.toFloat
  let fy := y.toFloat / cell.toFloat
  let ix := x / cell
  let iy := y / cell
  let tx := fx - ix.toFloat
  let ty := fy - iy.toFloat
  let sx := tx * tx * (3 - 2 * tx)
  let sy := ty * ty * (3 - 2 * ty)
  let a := hash ix iy s; let b := hash (ix + 1) iy s
  let c := hash ix (iy + 1) s; let d := hash (ix + 1) (iy + 1) s
  let top := a + (b - a) * sx
  let bot := c + (d - c) * sx
  top + (bot - top) * sy

/-- Terrain tile of map cell `(x, y)`. -/
def terrainAt (x y : Nat) : Nat :=
  let h := 0.65 * noise x y 8 11 + 0.35 * noise x y 3 12
  if h < 0.3 then (if hash x y 13 < 0.5 then 3 else 4)
  else if h < 0.35 then 2
  else if h > 0.72 then 6
  else if noise x y 6 14 > 0.62 then 5
  else let r := hash x y 15
    if r < 0.06 then 1 else if r < 0.08 then 7 else 0

def terrain : Array Nat := Id.run do
  let mut t := Array.emptyWithCapacity (mapSize * mapSize)
  for y in [0:mapSize] do
    for x in [0:mapSize] do
      t := t.push (terrainAt x y)
  return t

/-! ## Units -/

structure Unit where
  x : Float
  y : Float
  tx : Float
  ty : Float
  speed : Float
  team : Nat
deriving Inhabited

/-- A 64-bit LCG; `uniform` takes its top 53 bits. -/
@[inline] def nextRng (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
@[inline] def uniform (s : UInt64) : Float := (s >>> 11).toFloat / 9007199254740992

/-- Units wander inside this world rectangle (it fits a 1280 × 720 window at
zoom 1, so every unit is on screen by default). -/
def arena : Rect := ⟨worldSize / 2 - 600, worldSize / 2 - 320, 1200, 640⟩

def randomPoint (s : UInt64) : Float × Float × UInt64 :=
  let s1 := nextRng s
  let s2 := nextRng s1
  (arena.x + uniform s1 * arena.w, arena.y + uniform s2 * arena.h, s2)

def spawn (n : Nat) (seed : UInt64) : Array Unit × UInt64 := Id.run do
  let mut s := seed
  let mut us := Array.emptyWithCapacity n
  for i in [0:n] do
    let (x, y, s1) := randomPoint s
    let (tx, ty, s2) := randomPoint s1
    let s3 := nextRng s2
    us := us.push { x, y, tx, ty, speed := 30 + 40 * uniform s3, team := i % teamColors.size }
    s := s3
  return (us, s)

/-- Walk every unit `dt` seconds toward its target, picking a new target on arrival. -/
def walk (us : Array Unit) (seed : UInt64) (dt : Float) : Array Unit × UInt64 := Id.run do
  let mut s := seed
  let mut out := Array.emptyWithCapacity us.size
  for u in us do
    let dx := u.tx - u.x
    let dy := u.ty - u.y
    let d := Float.sqrt (dx * dx + dy * dy)
    let step := u.speed * dt
    if d <= step then
      let (tx, ty, s') := randomPoint s
      s := s'
      out := out.push { u with x := u.tx, y := u.ty, tx, ty }
    else
      out := out.push { u with x := u.x + dx / d * step, y := u.y + dy / d * step }
  return (out, s)

/-! ## App -/

inductive Msg where
  | input (e : Event)

structure Model where
  cam : Camera
  gestures : Gestures := {}
  units : Array Unit
  rng : UInt64
  time : Float := 0
  viewW : Float
  viewH : Float
  /-- Frames and seconds since the fps counter was last updated. -/
  frames : Nat := 0
  elapsed : Float := 0
  fps : Float := 0
  frameMs : Float := 0

def update : Msg → Model → Model
  | .input (.tick dt), m =>
    let dt' := Min.min dt 0.1
    let (units, rng) := walk m.units m.rng dt'
    let frames := m.frames + 1
    let elapsed := m.elapsed + dt
    let m := { m with units, rng, time := m.time + dt', frames, elapsed }
    if elapsed < 0.5 then m
    else { m with fps := frames.toFloat / elapsed, frameMs := elapsed * 1000 / frames.toFloat,
                  frames := 0, elapsed := 0 }
  | .input (.resize w h), m =>
    { m with viewW := w.toFloat, viewH := h.toFloat,
             cam := m.cam.clampTo w.toFloat h.toFloat worldSize worldSize }
  | .input e, m =>
    let (gestures, cam) := m.gestures.handle m.cam e
    { m with gestures, cam := cam.clampTo m.viewW m.viewH worldSize worldSize }

/-- Map cells `[lo, hi)` overlapping world interval `[a, a + len)`. -/
def cellRange (a len : Float) : Nat × Nat :=
  let t := tileSize.toFloat
  let lo := Max.max 0 (a / t).floor
  let hi := Min.min mapSize.toFloat ((a + len) / t).ceil
  (lo.toUInt64.toNat, if hi <= lo then lo.toUInt64.toNat else hi.toUInt64.toNat)

/-- The visible terrain tiles. Tiles are drawn one screen pixel larger than
their cell so that the anti-aliased edges of neighbours overlap instead of
letting the background show through the seams. -/
def tileSprites (cam : Camera) (vw vh : Float) : Array Sprite := Id.run do
  let v := cam.visible vw vh
  let (x0, x1) := cellRange v.x v.w
  let (y0, y1) := cellRange v.y v.h
  let t := tileSize.toFloat
  let pad := 1 / cam.zoom
  let mut out := Array.emptyWithCapacity ((x1 - x0) * (y1 - y0))
  for y in [y0:y1] do
    for x in [x0:x1] do
      let k := terrain[y * mapSize + x]!
      out := out.push { src := ⟨k.toFloat * t, 0, t, t⟩, dst := ⟨x.toFloat * t, y.toFloat * t, t + pad, t + pad⟩ }
  return out

/-- The visible units, back to front. Units stand on their feet: the sprite's
bottom center is the unit's position. -/
def unitSprites (cam : Camera) (vw vh : Float) (us : Array Unit) (time : Float) : Array Sprite :=
  let t := tileSize.toFloat
  let v := (cam.visible vw vh).inflate t
  let visible := us.filter fun u => v.contains ⟨u.x, u.y⟩
  let sorted := visible.qsort fun a b => a.y < b.y
  sorted.mapIdx fun i u =>
    let frame := ((time * 6).floor.toUInt64.toNat + i) % 2
    { src := ⟨((u.team * 2 + frame) * tileSize).toFloat, t, t, t⟩, dst := ⟨u.x - t / 2, u.y - t, t, t⟩ }

def fmt1 (v : Float) : String :=
  let r := (v * 10).round / 10
  let s := toString r
  match s.splitOn "." with
  | [a, b] => a ++ "." ++ (b.take 1)
  | _ => s

def hud (m : Model) (visible : Nat) : Array RenderOp :=
  let line := s!"{fmt1 m.fps} fps  {fmt1 m.frameMs} ms  {visible} units  zoom {fmt1 m.cam.zoom}"
  #[.fill (.roundedRect ⟨8, 8, (line.length * 12 + 16).toFloat, 30⟩ (.all 6)) (.solid (Color.rgba 0 0 0 0.55)),
    .text ⟨16, 15⟩ line 2 Color.white]

def view (m : Model) : UI.Widget Msg :=
  canvas 0 0 fun r =>
    let tiles := tileSprites m.cam r.w r.h
    let units := unitSprites m.cam r.w r.h m.units m.time
    #[.transform m.cam.affine #[.sprites atlas tiles, .sprites atlas units]] ++ hud m units.size

/-- `units` units in a `w × h` viewport, with the camera centered on the arena. -/
def app (w h : Nat) (units : Nat := 300) (zoom : Float := 1) : App Model Msg :=
  let (us, rng) := spawn units 42
  let vw := w.toFloat; let vh := h.toFloat
  let c := arena.center
  let cam : Camera := { x := c.x - vw / 2 / zoom, y := c.y - vh / 2 / zoom, zoom }
  { init := { cam := cam.clampTo vw vh worldSize worldSize, units := us, rng, viewW := vw, viewH := vh }
    update
    view
    subscriptions := fun e _ => some (.input e)
    animating := fun _ => true
    background := Color.rgb 0.29 0.55 0.24
    title := "uvl sprites" }

end Examples.Sprites
