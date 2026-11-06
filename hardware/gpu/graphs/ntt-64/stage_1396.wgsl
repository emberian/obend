// obend-emit-gpu: ntt-64, stage 1396 of 1670: 3 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[7284u + e] = select(i64(0), i64(1), u64(w[7276u + e]) < u64(w[7280u + e])); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[7288u + e] = w[7276u + e] + w[7264u + e]; }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[7292u + e] = w[7276u + e] - w[7280u + e]; }
}
