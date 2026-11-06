// obend-emit-gpu: glmul-4, stage 8 of 21: 2 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[84u + e] = w[72u + e] | w[80u + e]; }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[88u + e] = i64(u64(w[40u + e]) >> u32(w[16u + e])); }
}
