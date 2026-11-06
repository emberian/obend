// obend-emit-gpu: ntt-64, stage 819 of 1670: 3 kernels, 48 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 16u) { let e : u32 = t - 0u; w[4640u + e] = select(w[4624u + e], w[4608u + e], w[4592u + e] != i64(0)); }
  if (t >= 16u && t < 32u) { let e : u32 = t - 16u; w[4656u + e] = select(i64(0), i64(1), u64(w[2000u + e]) < u64(w[4560u + e])); }
  if (t >= 32u && t < 48u) { let e : u32 = t - 32u; w[4672u + e] = w[3888u + e] - w[4560u + e]; }
}
