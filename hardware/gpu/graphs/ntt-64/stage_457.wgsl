// obend-emit-gpu: ntt-64, stage 457 of 1670: 4 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[2180u + e] = w[2170u + e] * w[2172u + e]; }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[2182u + e] = w[2170u + e] * w[2174u + e]; }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[2184u + e] = i64(u64(w[2176u + e]) >> u32(w[2166u + e])); }
  if (t >= 6u && t < 8u) { let e : u32 = t - 6u; w[2186u + e] = w[2178u + e] & w[2164u + e]; }
}
