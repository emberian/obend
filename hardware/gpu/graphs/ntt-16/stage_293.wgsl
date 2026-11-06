// obend-emit-gpu: ntt-16, stage 293 of 398: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[1028u + e] = select(w[1027u + (e - 1u)], w[1022u + e], e < 1u); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[1030u + e] = w[970u + ix[62u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[1031u + e] = w[970u + ix[63u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[1032u + e] = c[68u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[1033u + e] = c[69u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[1034u + e] = c[70u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[1035u + e] = c[71u + e]; }
}
