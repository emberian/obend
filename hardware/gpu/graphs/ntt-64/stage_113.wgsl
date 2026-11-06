// obend-emit-gpu: ntt-64, stage 113 of 1670: 4 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[490u + e] = w[485u + e] * w[486u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[491u + e] = w[485u + e] * w[487u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[492u + e] = i64(u64(w[488u + e]) >> u32(w[483u + e])); }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[493u + e] = w[489u + e] & w[482u + e]; }
}
