// obend-emit-gpu: ntt-64, stage 1403 of 1670: 3 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[7336u + e] = select(w[7332u + e], w[7328u + e], w[7324u + e] != i64(0)); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[7340u + e] = select(i64(0), i64(1), u64(w[6908u + e]) < u64(w[7316u + e])); }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[7344u + e] = w[7148u + e] - w[7316u + e]; }
}
