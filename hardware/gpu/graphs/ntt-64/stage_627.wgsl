// obend-emit-gpu: ntt-64, stage 627 of 1670: 3 kernels, 3 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[2830u + e] = w[2829u + e] - w[2827u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[2831u + e] = select(i64(0), i64(1), u64(w[2820u + e]) < u64(w[2801u + e])); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[2832u + e] = w[2820u + e] - w[2801u + e]; }
}
