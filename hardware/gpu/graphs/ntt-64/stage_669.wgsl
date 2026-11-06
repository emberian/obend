// obend-emit-gpu: ntt-64, stage 669 of 1670: 4 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[2984u + e] = w[2979u + e] * w[2980u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[2985u + e] = w[2979u + e] * w[2981u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[2986u + e] = i64(u64(w[2982u + e]) >> u32(w[2977u + e])); }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[2987u + e] = w[2983u + e] & w[2976u + e]; }
}
