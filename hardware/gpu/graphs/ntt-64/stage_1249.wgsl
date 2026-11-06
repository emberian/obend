// obend-emit-gpu: ntt-64, stage 1249 of 1670: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[6740u + e] = select(w[6739u + (e - 1u)], w[6734u + e], e < 1u); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[6742u + e] = w[6682u + ix[350u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[6743u + e] = w[6682u + ix[351u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[6744u + e] = c[452u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[6745u + e] = c[453u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[6746u + e] = c[454u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[6747u + e] = c[455u + e]; }
}
