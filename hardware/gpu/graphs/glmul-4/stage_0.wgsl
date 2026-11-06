// obend-emit-gpu: glmul-4, stage 0 of 2: 3 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) {
    let e : u32 = t - 0u;
    w[8u + e] = c[0u + e];
  }
  if (t >= 4u && t < 8u) {
    let e : u32 = t - 4u;
    w[12u + e] = c[4u + e];
  }
  if (t >= 8u && t < 12u) {
    let e : u32 = t - 8u;
    w[16u + e] = c[8u + e];
  }
}
