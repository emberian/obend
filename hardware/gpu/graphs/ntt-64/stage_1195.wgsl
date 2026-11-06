// obend-emit-gpu: ntt-64, stage 1195 of 1670: 4 kernels, 32 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[6240u + e] = w[6200u + e] & w[6224u + e]; }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[6248u + e] = i64(u64(w[6200u + e]) >> u32(w[6232u + e])); }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[6256u + e] = w[6208u + e] & w[6224u + e]; }
  if (t >= 24u && t < 32u) { let e : u32 = t - 24u; w[6264u + e] = i64(u64(w[6208u + e]) >> u32(w[6232u + e])); }
}
