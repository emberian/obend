// obend-emit-gpu: ntt-64, stage 1332 of 1670: 2 kernels, 2 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[6990u + e] = w[6986u + e] & w[6978u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[6991u + e] = w[6988u + e] + w[6989u + e]; }
}
