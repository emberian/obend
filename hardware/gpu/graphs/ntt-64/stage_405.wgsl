// obend-emit-gpu: ntt-64, stage 405 of 1670: 4 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[2056u + e] = w[2051u + e] * w[2052u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[2057u + e] = w[2051u + e] * w[2053u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[2058u + e] = i64(u64(w[2054u + e]) >> u32(w[2049u + e])); }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[2059u + e] = w[2055u + e] & w[2048u + e]; }
}
