// obend-emit-gpu: glmul-4, stage 16 of 21: 3 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[144u + e] = select(i64(0), i64(1), u64(w[136u + e]) < u64(w[140u + e])); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[148u + e] = w[136u + e] + w[124u + e]; }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[152u + e] = w[136u + e] - w[140u + e]; }
}
