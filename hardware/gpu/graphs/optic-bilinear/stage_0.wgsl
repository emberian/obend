// obend-emit-gpu: optic-bilinear, stage 0 of 1: 3 kernels, 3 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) {
    let e : u32 = t - 0u;
    let v6 : i64 = w[0u + e] * w[1u + e];
    let v3 : i64 = c[0u] * v6;
    w[3u + e] = v3;
  }
  if (t >= 1u && t < 2u) {
    let e : u32 = t - 1u;
    let v7 : i64 = c[1u] * w[1u + e];
    let v4 : i64 = v7 * w[2u + e];
    w[4u + e] = v4;
  }
  if (t >= 2u && t < 3u) {
    let e : u32 = t - 2u;
    let v8 : i64 = c[2u] * w[0u + e];
    let v5 : i64 = v8 * w[2u + e];
    w[5u + e] = v5;
  }
}
