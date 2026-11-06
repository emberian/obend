// obend-emit-gpu: ntt-64, stage 110 of 1670: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[476u + e] = select(w[475u + (e - 1u)], w[470u + e], e < 1u); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[478u + e] = w[418u + ix[134u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[479u + e] = w[418u + ix[135u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[480u + e] = c[20u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[481u + e] = c[21u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[482u + e] = c[22u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[483u + e] = c[23u + e]; }
}
