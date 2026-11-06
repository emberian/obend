// obend-emit-gpu: optic-bilinear, stage 2 of 4: 2 kernels, 2 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[4u + e] = w[7u + e] * w[2u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[8u + e] = c[2u] * w[0u + e]; }
}
