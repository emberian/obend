// obend-emit-gpu: ntt-64, stage 158 of 1670: 3 kernels, 6 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[626u + e] = select(i64(0), i64(1), u64(w[476u + e]) < u64(w[624u + e])); }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[628u + e] = w[476u + e] + w[622u + e]; }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[630u + e] = w[476u + e] - w[624u + e]; }
}
