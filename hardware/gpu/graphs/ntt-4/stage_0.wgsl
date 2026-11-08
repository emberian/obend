// obend-emit-gpu: ntt-4, stage 0 of 7: 6 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) {
    let e : u32 = t - 0u;
    w[4u + e] = c[0u + e];
  }
  if (t >= 2u && t < 4u) {
    let e : u32 = t - 2u;
    w[6u + e] = c[2u + e];
  }
  if (t >= 4u && t < 6u) {
    let e : u32 = t - 4u;
    w[8u + e] = c[4u + e];
  }
  if (t >= 6u && t < 8u) {
    let e : u32 = t - 6u;
    w[10u + e] = c[6u + e];
  }
  if (t >= 8u && t < 10u) {
    let e : u32 = t - 8u;
    w[12u + e] = w[0u + ix[0u + e]];
  }
  if (t >= 10u && t < 12u) {
    let e : u32 = t - 10u;
    w[14u + e] = w[0u + ix[2u + e]];
  }
}
