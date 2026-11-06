// obend-emit-gpu: ntt-64, stage 1278 of 1670: 4 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[6820u + e] = w[6810u + e] * w[6812u + e]; }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[6822u + e] = w[6810u + e] * w[6814u + e]; }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[6824u + e] = i64(u64(w[6816u + e]) >> u32(w[6806u + e])); }
  if (t >= 6u && t < 8u) { let e : u32 = t - 6u; w[6826u + e] = w[6818u + e] & w[6804u + e]; }
}
