// obend-emit-gpu: diamond, stage 0 of 1: 1 kernels, 1 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) {
    let e : u32 = t - 0u;
    let v4 : i64 = w[0u + e] + w[1u + e];
    let v5 : i64 = w[2u + e] + w[3u + e];
    let v6 : i64 = v4 * v5;
    let v7 : i64 = c[0u] + i64(0);
    let v8 : i64 = v6 + v7;
    w[8u + e] = v8;
  }
}
