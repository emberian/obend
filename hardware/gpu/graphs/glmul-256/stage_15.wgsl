// obend-emit-gpu: glmul-256, stage 15 of 21: 2 kernels, 512 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 256u) { let e : u32 = t - 0u; w[8704u + e] = select(w[8448u + e], w[5376u + e], w[8192u + e] != i64(0)); }
  if (t >= 256u && t < 512u) { let e : u32 = t - 256u; w[8960u + e] = w[512u + e] - w[7936u + e]; }
}
