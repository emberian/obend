// obend-emit-gpu: ntt-16, stage 0 of 13: 6 kernels, 48 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) {
    let e : u32 = t - 0u;
    w[16u + e] = c[0u + e];
  }
  if (t >= 8u && t < 16u) {
    let e : u32 = t - 8u;
    w[24u + e] = c[8u + e];
  }
  if (t >= 16u && t < 24u) {
    let e : u32 = t - 16u;
    w[32u + e] = c[16u + e];
  }
  if (t >= 24u && t < 32u) {
    let e : u32 = t - 24u;
    w[40u + e] = c[24u + e];
  }
  if (t >= 32u && t < 40u) {
    let e : u32 = t - 32u;
    w[48u + e] = w[0u + ix[0u + e]];
  }
  if (t >= 40u && t < 48u) {
    let e : u32 = t - 40u;
    w[56u + e] = w[0u + ix[8u + e]];
  }
}
