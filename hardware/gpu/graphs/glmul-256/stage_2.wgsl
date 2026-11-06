// obend-emit-gpu: glmul-256, stage 2 of 21: 2 kernels, 512 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 256u) { let e : u32 = t - 0u; w[2304u + e] = w[1280u + e] * w[1792u + e]; }
  if (t >= 256u && t < 512u) { let e : u32 = t - 256u; w[2560u + e] = w[1280u + e] * w[2048u + e]; }
}
