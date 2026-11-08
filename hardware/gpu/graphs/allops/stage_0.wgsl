// obend-emit-gpu: allops, stage 0 of 1: 3 kernels, 3 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) {
    let e : u32 = t - 0u;
    let v3 : i64 = c[0u] * w[0u + e];
    let v4 : i64 = w[1u + e] * w[2u + e] + w[0u + e];
    let v6 : i64 = v3 - v4;
    let v5 : i64 = c[1u] + i64(0);
    let v7 : i64 = v6 * v5;
    let v8 : i64 = v7 + v3;
    w[8u + e] = v8;
  }
  if (t >= 1u && t < 2u) {
    let e : u32 = t - 1u;
    let v4 : i64 = w[1u + e] * w[2u + e] + w[0u + e];
    let v9 : i64 = c[2u] * v4;
    w[9u + e] = v9;
  }
  if (t >= 2u && t < 3u) {
    let e : u32 = t - 2u;
    let v3 : i64 = c[3u] * w[0u + e];
    let v4 : i64 = w[1u + e] * w[2u + e] + w[0u + e];
    let v6 : i64 = v3 - v4;
    let v5 : i64 = c[4u] + i64(0);
    let v7 : i64 = v6 * v5;
    let v8 : i64 = v7 + v3;
    let v9 : i64 = c[5u] * v4;
    let v10 : i64 = select(v9, v8, w[0u + e] != i64(0));
    w[10u + e] = v10;
  }
}
