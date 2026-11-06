// obend-emit-gpu: ntt-16, stage 82 of 398: 7 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[274u + e] = w[36u + ix[34u + e]]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[276u + e] = w[272u + ix[36u + e]]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[277u + e] = w[272u + ix[37u + e]]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[278u + e] = c[16u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[279u + e] = c[17u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[280u + e] = c[18u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[281u + e] = c[19u + e]; }
}
