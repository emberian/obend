// obend-emit-gpu: ntt-64, stage 28 of 1670: 3 kernels, 3 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[238u + e] = select(w[237u + e], w[236u + e], w[235u + e] != i64(0)); }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[239u + e] = select(i64(0), i64(1), u64(w[188u + e]) < u64(w[233u + e])); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[240u + e] = w[191u + e] - w[233u + e]; }
}
