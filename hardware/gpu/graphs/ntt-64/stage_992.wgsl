// obend-emit-gpu: ntt-64, stage 992 of 1670: 3 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[5376u + e] = i64(u64(w[5328u + e]) >> u32(w[5300u + e])); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[5380u + e] = i64(u64(w[5352u + e]) >> u32(w[5300u + e])); }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[5384u + e] = w[5332u + e] + w[5372u + e]; }
}
