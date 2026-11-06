// obend-emit-gpu: ntt-64, stage 924 of 1670: 2 kernels, 2 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[5103u + e] = w[5102u + e] + w[5100u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[5104u + e] = w[5100u + e] - w[5090u + e]; }
}
