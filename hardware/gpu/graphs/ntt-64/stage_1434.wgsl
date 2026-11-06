// obend-emit-gpu: ntt-64, stage 1434 of 1670: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[7436u + e] = select(w[7435u + (e - 1u)], w[7430u + e], e < 1u); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[7438u + e] = w[7378u + ix[374u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[7439u + e] = w[7378u + ix[375u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[7440u + e] = c[500u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[7441u + e] = c[501u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[7442u + e] = c[502u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[7443u + e] = c[503u + e]; }
}
