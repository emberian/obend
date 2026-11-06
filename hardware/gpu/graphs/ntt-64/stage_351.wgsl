// obend-emit-gpu: ntt-64, stage 351 of 1670: 2 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[1400u + e] = w[1384u + e] & w[1352u + e]; }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[1404u + e] = w[1392u + e] + w[1396u + e]; }
}
