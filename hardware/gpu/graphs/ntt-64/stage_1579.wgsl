// obend-emit-gpu: ntt-64, stage 1579 of 1670: 3 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[7960u + e] = w[7956u + e] - w[7948u + e]; }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[7964u + e] = select(i64(0), i64(1), u64(w[7920u + e]) < u64(w[7844u + e])); }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[7968u + e] = w[7920u + e] - w[7844u + e]; }
}
