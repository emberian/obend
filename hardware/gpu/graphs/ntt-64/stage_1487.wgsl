// obend-emit-gpu: ntt-64, stage 1487 of 1670: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[7610u + e] = w[7372u + ix[378u + e]]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[7612u + e] = w[7608u + ix[380u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[7613u + e] = w[7608u + ix[381u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[7614u + e] = c[512u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[7615u + e] = c[513u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[7616u + e] = c[514u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[7617u + e] = c[515u + e]; }
}
