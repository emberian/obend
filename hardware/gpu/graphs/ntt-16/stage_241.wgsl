// obend-emit-gpu: ntt-16, stage 241 of 398: 4 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[864u + e] = w[854u + e] & w[860u + e]; }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[866u + e] = i64(u64(w[854u + e]) >> u32(w[862u + e])); }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[868u + e] = w[856u + e] & w[860u + e]; }
  if (t >= 6u && t < 8u) { let e : u32 = t - 6u; w[870u + e] = i64(u64(w[856u + e]) >> u32(w[862u + e])); }
}
