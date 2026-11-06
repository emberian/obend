// obend-emit-gpu: ntt-64, stage 171 of 1670: 3 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[736u + e] = i64(u64(w[688u + e]) >> u32(w[660u + e])); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[740u + e] = i64(u64(w[712u + e]) >> u32(w[660u + e])); }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[744u + e] = w[692u + e] + w[732u + e]; }
}
