// obend-emit-gpu: ntt-64, stage 374 of 1670: 4 kernels, 32 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[1600u + e] = w[1560u + e] & w[1584u + e]; }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[1608u + e] = i64(u64(w[1560u + e]) >> u32(w[1592u + e])); }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[1616u + e] = w[1568u + e] & w[1584u + e]; }
  if (t >= 24u && t < 32u) { let e : u32 = t - 24u; w[1624u + e] = i64(u64(w[1568u + e]) >> u32(w[1592u + e])); }
}
