// obend-emit-gpu: ntt-16, stage 374 of 398: 4 kernels, 32 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[1504u + e] = w[1464u + e] * w[1472u + e]; }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[1512u + e] = w[1464u + e] * w[1480u + e]; }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[1520u + e] = i64(u64(w[1488u + e]) >> u32(w[1448u + e])); }
  if (t >= 24u && t < 32u) { let e : u32 = t - 24u; w[1528u + e] = w[1496u + e] & w[1440u + e]; }
}
