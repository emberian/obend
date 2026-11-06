// obend-emit-gpu: glmul-256, stage 16 of 21: 3 kernels, 768 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 256u) { let e : u32 = t - 0u; w[9216u + e] = select(i64(0), i64(1), u64(w[8704u + e]) < u64(w[8960u + e])); }
  if (t >= 256u && t < 512u) { let e : u32 = t - 256u; w[9472u + e] = w[8704u + e] + w[7936u + e]; }
  if (t >= 512u && t < 768u) { let e : u32 = t - 512u; w[9728u + e] = w[8704u + e] - w[8960u + e]; }
}
