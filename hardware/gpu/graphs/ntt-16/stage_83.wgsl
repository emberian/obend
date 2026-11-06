// obend-emit-gpu: ntt-16, stage 83 of 398: 4 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[282u + e] = w[277u + e] & w[280u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[283u + e] = i64(u64(w[277u + e]) >> u32(w[281u + e])); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[284u + e] = w[278u + e] & w[280u + e]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[285u + e] = i64(u64(w[278u + e]) >> u32(w[281u + e])); }
}
