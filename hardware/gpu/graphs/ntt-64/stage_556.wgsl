// obend-emit-gpu: ntt-64, stage 556 of 1670: 3 kernels, 6 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[2488u + e] = select(w[2486u + e], w[2484u + e], w[2482u + e] != i64(0)); }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[2490u + e] = select(i64(0), i64(1), u64(w[2332u + e]) < u64(w[2478u + e])); }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[2492u + e] = w[2394u + e] - w[2478u + e]; }
}
