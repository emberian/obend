// obend-emit-gpu: ntt-64, stage 759 of 1670: 2 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[3332u + e] = select(w[3328u + e], w[3280u + e], w[3324u + e] != i64(0)); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[3336u + e] = w[3204u + e] - w[3320u + e]; }
}
