// obend-emit-gpu: ntt-64, stage 1435 of 1670: 4 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[7444u + e] = w[7439u + e] & w[7442u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[7445u + e] = i64(u64(w[7439u + e]) >> u32(w[7443u + e])); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[7446u + e] = w[7440u + e] & w[7442u + e]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[7447u + e] = i64(u64(w[7440u + e]) >> u32(w[7443u + e])); }
}
