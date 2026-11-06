// obend-emit-gpu: optic-mul, stage 0 of 1: 3 kernels, 3 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[3u + e] = w[0u + e] * w[1u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[4u + e] = w[1u + e] * w[2u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[5u + e] = w[0u + e] * w[2u + e]; }
}
