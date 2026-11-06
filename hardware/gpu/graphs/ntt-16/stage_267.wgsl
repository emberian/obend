// obend-emit-gpu: ntt-16, stage 267 of 398: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[970u + e] = w[732u + ix[58u + e]]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[972u + e] = w[968u + ix[60u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[973u + e] = w[968u + ix[61u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[974u + e] = c[64u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[975u + e] = c[65u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[976u + e] = c[66u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[977u + e] = c[67u + e]; }
}
