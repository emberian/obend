// obend-emit-gpu: ntt-64, stage 1621 of 1670: 2 kernels, 32 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 16u) { let e : u32 = t - 0u; w[8736u + e] = w[8672u + e] & w[8544u + e]; }
  if (t >= 16u && t < 32u) { let e : u32 = t - 16u; w[8752u + e] = w[8704u + e] + w[8720u + e]; }
}
