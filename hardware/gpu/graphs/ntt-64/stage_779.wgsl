// obend-emit-gpu: ntt-64, stage 779 of 1670: 3 kernels, 24 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[3600u + e] = i64(u64(w[3504u + e]) >> u32(w[3448u + e])); }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[3608u + e] = i64(u64(w[3552u + e]) >> u32(w[3448u + e])); }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[3616u + e] = w[3512u + e] + w[3592u + e]; }
}
