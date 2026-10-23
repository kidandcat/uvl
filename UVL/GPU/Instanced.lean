import UVL.GPU.Kernels

/-!
# Instanced sprites and the scaled-world blit (native hosts)

WGSL appended to `shaderSource` by the native GPU host (`native/gpu_shell.c`):

* `vs_isprite`/`fs_isprite` draw a `kindSpriteRun` (see `Batch.pushRun`) as
  instanced quads sampled from a hardware texture: the run's marker primitive
  (slot 8–13 forward transform) is read from `prims`, the quads from the
  instance buffer of group 1. The texture holds premultiplied RGBA8 and is
  sampled nearest (`textureLoad`) or bilinear clamped to the sprite's texel
  rectangle, like `Texture.sampleNearest`/`sampleLinear`.
* `vs_blit`/`fs_blit` upscale the world target of a split frame
  (`Batch.buildSplit`) onto the screen with a linear sampler.

The browser host and the interpreted reference renderer never see these
kinds: batches are lowered with `instanced := false` for them.
-/

namespace UVL.GPU

/-- The WGSL of the instanced sprite and blit pipelines. It uses `prims` and
`screen` of the uber module, so it must follow `shaderSource`. -/
def instancedSource : String := "
// Instanced sprites and blit (GPU/Instanced.lean).
@group(1) @binding(0) var<storage, read> inst : array<f32>;
@group(1) @binding(1) var sprite_tex : texture_2d<f32>;
@group(1) @binding(2) var sprite_samp : sampler;
@group(1) @binding(5) var blit_tex : texture_2d<f32>;
@group(1) @binding(6) var blit_samp : sampler;

struct SpriteOut {
  @builtin(position) pos : vec4f,
  @location(0) uv : vec2f,
  @location(1) @interpolate(flat) lo : vec4f,
  @location(2) @interpolate(flat) op : vec2f,
}

@vertex fn vs_isprite(@builtin(vertex_index) v : u32, @builtin(instance_index) i : u32) -> SpriteOut {
  let rb = (v / 6u) * 36u;
  let k = v % 6u;
  let ux = select(0.0, 1.0, k == 1u || k == 4u || k == 5u);
  let uy = select(0.0, 1.0, k == 2u || k == 3u || k == 5u);
  let b = i * 12u;
  let lx = inst[b] + inst[b + 2u] * ux;
  let ly = inst[b + 1u] + inst[b + 3u] * uy;
  let dx = prims[rb + 8u] * lx + prims[rb + 10u] * ly + prims[rb + 12u];
  let dy = prims[rb + 9u] * lx + prims[rb + 11u] * ly + prims[rb + 13u];
  var out : SpriteOut;
  out.pos = vec4f(dx / screen.x * 2.0 - 1.0, 1.0 - dy / screen.y * 2.0, 0.0, 1.0);
  let sx = inst[b + 4u];
  let sy = inst[b + 5u];
  let sw = inst[b + 6u];
  let sh = inst[b + 7u];
  out.uv = vec2f(sx + sw * ux, sy + sh * uy);
  out.lo = vec4f(sx, sy, sx + sw, sy + sh);
  out.op = vec2f(inst[b + 8u], inst[b + 9u]);
  return out;
}

@fragment fn fs_isprite(in : SpriteOut) -> @location(0) vec4f {
  var c : vec4f;
  if (in.op.y > 0.5) {
    let dim = vec2f(textureDimensions(sprite_tex));
    let uv = clamp(in.uv, in.lo.xy + vec2f(0.5), in.lo.zw - vec2f(0.5));
    c = textureSampleLevel(sprite_tex, sprite_samp, uv / dim, 0.0);
  } else {
    let t = clamp(floor(in.uv), in.lo.xy, in.lo.zw - vec2f(1.0));
    c = textureLoad(sprite_tex, vec2i(t), 0);
  }
  return c * in.op.x;
}

struct BlitOut {
  @builtin(position) pos : vec4f,
  @location(0) uv : vec2f,
}

@vertex fn vs_blit(@builtin(vertex_index) v : u32) -> BlitOut {
  let x = f32((v << 1u) & 2u);
  let y = f32(v & 2u);
  var out : BlitOut;
  out.pos = vec4f(x * 2.0 - 1.0, 1.0 - y * 2.0, 0.0, 1.0);
  out.uv = vec2f(x, y);
  return out;
}

@fragment fn fs_blit(in : BlitOut) -> @location(0) vec4f {
  return textureSampleLevel(blit_tex, blit_samp, in.uv, 0.0);
}
"

/-- The module native hosts compile: the uber kernels plus the instanced
pipelines. -/
def nativeShaderSource : String := shaderSource ++ instancedSource

end UVL.GPU
