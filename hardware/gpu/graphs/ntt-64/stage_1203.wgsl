// obend-emit-gpu: ntt-64, stage 1203 of 1670: 3 kernels, 24 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[6384u + e] = i64(u64(w[6288u + e]) >> u32(w[6232u + e])); }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[6392u + e] = i64(u64(w[6336u + e]) >> u32(w[6232u + e])); }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[6400u + e] = w[6296u + e] + w[6376u + e]; }
}
