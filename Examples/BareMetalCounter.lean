import Examples.Counter
import UniversalViz.BareMetal.Shell

/-!
The counter app exported for microcontrollers: the same `Examples.Counter.app`
that runs on the desktop, behind the C ABI declared in `baremetal/include/uvl.h`.
`lake build Examples.BareMetalCounter:c` produces the C files that the firmware
compiles together with `baremetal/rt/uvl_rt.c` (no `libleanrt`).
-/

namespace Examples.BareMetalCounter
open UViz BareMetal

abbrev S := Shell Counter.Model Counter.Msg

@[export uvl_init]
def init (w h tw th : UInt16) : S :=
  Shell.start Counter.app { width := w.toNat, height := h.toNat, tileW := tw.toNat, tileH := th.toNat }

@[export uvl_event]
def event (s : S) (kind : UInt8) (a b : UInt16) : S := s.event kind a b

@[export uvl_needs_redraw]
def needsRedraw (s : S) : UInt8 := if s.needsRedraw then 1 else 0

@[export uvl_begin_frame]
def beginFrame (s : S) : S := s.beginFrame

@[export uvl_tile_rgb565]
def tileRGB565 (s : S) (tx ty : UInt16) : ByteArray := s.tileRGB565 tx ty

@[export uvl_tile_mono]
def tileMono (s : S) (tx ty : UInt16) : ByteArray := s.tileMono tx ty

/-- Desktop check: the whole frame through the exported tile function. -/
def frameRGB565 (s : S) : ByteArray :=
  Tile.origins s.cfg.width s.cfg.height s.cfg.tileW s.cfg.tileH |>.foldl
    (init := ByteArray.mk (Array.replicate (2 * s.cfg.width * s.cfg.height) 0)) fun acc (tx, ty) =>
      let tile := tileRGB565 s tx.toUInt16 ty.toUInt16
      let cw := Tile.extent s.cfg.width s.cfg.tileW tx
      let ch := Tile.extent s.cfg.height s.cfg.tileH ty
      (List.range ch).foldl (init := acc) fun acc row =>
        tile.copySlice (row * cw * 2) acc (((ty + row) * s.cfg.width + tx) * 2) (cw * 2)

end Examples.BareMetalCounter
