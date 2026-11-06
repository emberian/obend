// obend-emit-gpu: adjoint-square-bilinear, stage 0 of 1: 3 kernels, 3 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) {
    let e : u32 = t - 0u;
    let v2 : i64 = w[0u + e] * w[0u + e];
    let v5 : i64 = v2 * w[1u + e];
    let v3 : i64 = c[0u] * v5;
    w[3u + e] = v3;
  }
  if (t >= 1u && t < 2u) {
    let e : u32 = t - 1u;
    let v2 : i64 = w[0u + e] * w[0u + e];
    let v7 : i64 = c[1u] * w[6u + e];
    let v9 : i64 = v2 * v7;
    w[9u + e] = v9;
  }
  if (t >= 2u && t < 3u) {
    let e : u32 = t - 2u;
    let v7 : i64 = c[2u] * w[6u + e];
    let v8 : i64 = w[1u + e] * v7;
    let v10 : i64 = w[0u + e] * v8;
    let v11 : i64 = w[0u + e] * v8;
    let v12 : i64 = v10 + v11;
    w[12u + e] = v12;
  }
}
