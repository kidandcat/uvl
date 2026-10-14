import UVL.App.Runtime
import UVL.Render.Tile

/-!
# Bare-metal shell

Inverted FFI contract for microcontrollers: Lean never touches SPI, I2C, GPIO or
timers. The C main loop owns the hardware and *asks* Lean for two things:

1. fold an input event (button, rotary encoder, touch) into the UI state;
2. render one tile of the current frame into a small buffer that DMA streams to
   the panel while Lean computes the next tile.

`Shell` bundles the pure `Runtime` with the display geometry and the binned
scene of the current frame (built once per frame, queried per tile). An app
exports a monomorphic instance of these functions with `@[export]` (see
`Examples/BareMetalCounter.lean`); `baremetal/include/uvl.h` declares them for C.

Event encoding (`kind`, `a`, `b`), mirrored by `UVL_EV_*` in `uvl.h`:

| kind | meaning              | a, b              |
|------|----------------------|-------------------|
| 0    | none                 |                   |
| 1    | touch / pointer down | x, y (pixels)     |
| 2    | touch / pointer move | x, y              |
| 3    | touch / pointer up   | x, y              |
| 4    | key down             | key code, –       |
| 5    | key up               | key code, –       |
| 6    | tick                 | milliseconds, –   |

Key codes: 1 up, 2 down, 3 left, 4 right, 5 enter, 6 back/escape, ≥ 32 a character.
-/

namespace UVL.BareMetal

structure Config where
  width : Nat
  height : Nat
  tileW : Nat := 64
  tileH : Nat := 16
  /-- Evaluate shapes in Q16.16 fixed point (no FPU needed for the per-pixel work). -/
  fixedPoint : Bool := true
deriving Inhabited, Repr

structure Shell (Model Msg : Type) where
  rt : Runtime Model Msg
  cfg : Config
  /-- Binned scene of the frame being streamed. -/
  scene : TileList

namespace Shell

variable {Model Msg : Type}

def sceneOf (rt : Runtime Model Msg) : TileList :=
  TileList.build (rt.tree.2.toOps 0 0 rt.pointerState)

def start (app : App Model Msg) (cfg : Config) : Shell Model Msg :=
  let rt := Runtime.start app cfg.width cfg.height
  { rt, cfg, scene := sceneOf rt }

def decodeKey (code : UInt16) : Key :=
  match code with
  | 1 => .up | 2 => .down | 3 => .left | 4 => .right | 5 => .enter | 6 => .escape
  | c => if c >= 32 then .char (Char.ofNat c.toNat) else .other c.toNat

def decodeEvent (kind : UInt8) (a b : UInt16) : Option Event :=
  let x := a.toNat.toFloat; let y := b.toNat.toFloat
  match kind with
  | 1 => some (.pointerDown x y .left)
  | 2 => some (.pointerMove x y)
  | 3 => some (.pointerUp x y .left)
  | 4 => some (.keyDown (decodeKey a))
  | 5 => some (.keyUp (decodeKey a))
  | 6 => some (.tick (a.toNat.toFloat / 1000.0))
  | _ => none

/-- Feed one hardware event. -/
def event (s : Shell Model Msg) (kind : UInt8) (a b : UInt16) : Shell Model Msg :=
  match decodeEvent kind a b with
  | some e => { s with rt := s.rt.handle e }
  | none => s

/-- Whether the UI changed since the last `beginFrame`. -/
def needsRedraw (s : Shell Model Msg) : Bool := s.rt.dirty

/-- Freeze the scene for the frame about to be streamed. -/
def beginFrame (s : Shell Model Msg) : Shell Model Msg :=
  { s with scene := sceneOf s.rt, rt := { s.rt with dirty := false } }

def tileExtent (s : Shell Model Msg) (tx ty : UInt16) : Nat × Nat :=
  (Tile.extent s.cfg.width s.cfg.tileW tx.toNat, Tile.extent s.cfg.height s.cfg.tileH ty.toNat)

/-- Tile at device pixel `(tx, ty)` as big-endian RGB565 (`2 · tw · th` bytes;
edge tiles are smaller). -/
def tileRGB565 (s : Shell Model Msg) (tx ty : UInt16) : ByteArray :=
  Tile.renderRGB565 s.scene s.cfg.width s.cfg.height s.cfg.tileW s.cfg.tileH tx.toNat ty.toNat
    s.rt.app.background s.cfg.fixedPoint

/-- Tile at `(tx, ty)` packed SSD1306-style (`tw · ⌈th / 8⌉` bytes). -/
def tileMono (s : Shell Model Msg) (tx ty : UInt16) : ByteArray :=
  (Tile.render s.scene s.cfg.width s.cfg.height s.cfg.tileW s.cfg.tileH tx.toNat ty.toNat
    s.rt.app.background s.cfg.fixedPoint).toMonoPages

end Shell

end UVL.BareMetal
