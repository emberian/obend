// obend-emit-gpu: ntt-64, stage 389 of 1670: 3 kernels, 24 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[1848u + e] = select(i64(0), i64(1), u64(w[1832u + e]) < u64(w[1840u + e])); }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[1856u + e] = w[1832u + e] + w[1808u + e]; }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[1864u + e] = w[1832u + e] - w[1840u + e]; }
}
