// obend-emit-gpu: ntt-64, stage 348 of 1670: 4 kernels, 16 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[1360u + e] = w[1340u + e] & w[1352u + e]; }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[1364u + e] = i64(u64(w[1340u + e]) >> u32(w[1356u + e])); }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[1368u + e] = w[1344u + e] & w[1352u + e]; }
  if (t >= 12u && t < 16u) { let e : u32 = t - 12u; w[1372u + e] = i64(u64(w[1344u + e]) >> u32(w[1356u + e])); }
}
