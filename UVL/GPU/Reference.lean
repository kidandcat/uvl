import UVL.GPU.Batch

/-!
# Reference GPU renderer

Runs the GPU pipeline on the CPU: the scene is lowered with `Batch.build`, and
for every pixel of every primitive's rectangle the generated `shade` function
is *evaluated in Lean* (`Stmt.run`, the DSL's semantics) and blended with
`FrameBuffer.blend`, as the GPU's blend unit would.

It is slow (an interpreter per pixel) and only meant for tests: comparing it
with `Raster.render` checks the lowering and the shader logic without a GPU.
What remains between it and real hardware is 32-bit float rounding.
-/

namespace UVL.GPU

/-- Render a scene through the GPU program, interpreted. -/
def referenceRender (w h : Nat) (ops : Array RenderOp) (bg : Color := Color.white) :
    FrameBuffer w h := Id.run do
  let b := Batch.build w h ops
  let atlas := b.atlasData
  let buffers := fun n =>
    if n == "prims" then b.prims else if n == "data" then b.data
    else if n == "atlas" then atlas else .empty
  let mut fb := FrameBuffer.new w h bg
  for i in [0:b.count] do
    let base := i * primStride
    let q (k : Nat) : Nat := b.prims[base + k]!.toUInt64.toNat
    for y in [q 5:q 7] do
      for x in [q 4:q 6] do
        if hx : x < w then
          if hy : y < h then
            let args : List Value := [⟨.u32, i.toUInt32⟩, ⟨.v2, ⟨x.toF + 0.5, y.toF + 0.5⟩⟩]
            match shadeDef.1.eval functions args buffers with
            | ⟨.v4, c⟩ => fb := fb.blend ⟨x, hx⟩ ⟨y, hy⟩ ⟨c.x, c.y, c.z, c.w⟩ 1.0
            | _ => pure ()
  return fb

end UVL.GPU
