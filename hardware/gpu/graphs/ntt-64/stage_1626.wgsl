// obend-emit-gpu: ntt-64, stage 1626 of 1670: 3 kernels, 48 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 16u) { let e : u32 = t - 0u; w[8864u + e] = i64(u64(w[8672u + e]) >> u32(w[8560u + e])); }
  if (t >= 16u && t < 32u) { let e : u32 = t - 16u; w[8880u + e] = i64(u64(w[8768u + e]) >> u32(w[8560u + e])); }
  if (t >= 32u && t < 48u) { let e : u32 = t - 32u; w[8896u + e] = w[8688u + e] + w[8848u + e]; }
}
