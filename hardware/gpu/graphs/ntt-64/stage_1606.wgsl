// obend-emit-gpu: ntt-64, stage 1606 of 1670: 2 kernels, 16 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[8328u + e] = select(w[8320u + e], w[8224u + e], w[8312u + e] != i64(0)); }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[8336u + e] = w[8072u + e] - w[8304u + e]; }
}
