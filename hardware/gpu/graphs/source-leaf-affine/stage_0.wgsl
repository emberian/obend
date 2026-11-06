// obend-emit-gpu: source-leaf-affine, stage 0 of 1: 1 kernels, 11 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 11u) {
    let e : u32 = t - 0u;
    let v1 : i64 = c[0u] + i64(0);
    let v2 : i64 = w[0u + e] * v1;
    let v3 : i64 = c[1u] + i64(0);
    let v4 : i64 = v2 + v3;
    w[44u + e] = v4;
  }
}
