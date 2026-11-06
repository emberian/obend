// obend-emit-gpu: ntt-4, stage 2 of 80: 4 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[14u + e] = w[9u + e] & w[12u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[15u + e] = i64(u64(w[9u + e]) >> u32(w[13u + e])); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[16u + e] = w[10u + e] & w[12u + e]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[17u + e] = i64(u64(w[10u + e]) >> u32(w[13u + e])); }
}
