// obend-emit-gpu: ntt-64, stage 1592 of 1670: 4 kernels, 32 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[8096u + e] = w[8056u + e] & w[8080u + e]; }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[8104u + e] = i64(u64(w[8056u + e]) >> u32(w[8088u + e])); }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[8112u + e] = w[8064u + e] & w[8080u + e]; }
  if (t >= 24u && t < 32u) { let e : u32 = t - 24u; w[8120u + e] = i64(u64(w[8064u + e]) >> u32(w[8088u + e])); }
}
