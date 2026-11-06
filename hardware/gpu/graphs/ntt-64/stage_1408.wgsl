// obend-emit-gpu: ntt-64, stage 1408 of 1670: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[7378u + e] = w[7368u + ix[370u + e]]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[7380u + e] = w[7376u + ix[372u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[7381u + e] = w[7376u + ix[373u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[7382u + e] = c[496u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[7383u + e] = c[497u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[7384u + e] = c[498u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[7385u + e] = c[499u + e]; }
}
