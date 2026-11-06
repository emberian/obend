// obend-emit-gpu: ntt-64, stage 139 of 1670: 4 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[556u + e] = w[546u + e] * w[548u + e]; }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[558u + e] = w[546u + e] * w[550u + e]; }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[560u + e] = i64(u64(w[552u + e]) >> u32(w[542u + e])); }
  if (t >= 6u && t < 8u) { let e : u32 = t - 6u; w[562u + e] = w[554u + e] & w[540u + e]; }
}
