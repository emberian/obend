// obend-emit-gpu: ntt-64, stage 295 of 1670: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[1172u + e] = select(w[1171u + (e - 1u)], w[1166u + e], e < 1u); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[1174u + e] = w[1114u + ix[158u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[1175u + e] = w[1114u + ix[159u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[1176u + e] = c[68u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[1177u + e] = c[69u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[1178u + e] = c[70u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[1179u + e] = c[71u + e]; }
}
