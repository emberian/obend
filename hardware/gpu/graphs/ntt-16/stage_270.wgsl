// obend-emit-gpu: ntt-16, stage 270 of 398: 4 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[984u + e] = w[979u + e] * w[980u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[985u + e] = w[979u + e] * w[981u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[986u + e] = i64(u64(w[982u + e]) >> u32(w[977u + e])); }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[987u + e] = w[983u + e] & w[976u + e]; }
}
