// obend-emit-gpu: ntt-16, stage 394 of 398: 3 kernels, 24 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[1808u + e] = select(w[1800u + e], w[1792u + e], w[1784u + e] != i64(0)); }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[1816u + e] = select(i64(0), i64(1), u64(w[720u + e]) < u64(w[1768u + e])); }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[1824u + e] = w[1432u + e] - w[1768u + e]; }
}
