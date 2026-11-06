// obend-emit-gpu: ntt-64, stage 1399 of 1670: 2 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[7308u + e] = w[7304u + e] + w[7296u + e]; }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[7312u + e] = w[7296u + e] - w[7256u + e]; }
}
