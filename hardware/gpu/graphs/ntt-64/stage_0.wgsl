// obend-emit-gpu: ntt-64, stage 0 of 19: 6 kernels, 192 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 32u) {
    let e : u32 = t - 0u;
    w[64u + e] = c[0u + e];
  }
  if (t >= 32u && t < 64u) {
    let e : u32 = t - 32u;
    w[96u + e] = c[32u + e];
  }
  if (t >= 64u && t < 96u) {
    let e : u32 = t - 64u;
    w[128u + e] = c[64u + e];
  }
  if (t >= 96u && t < 128u) {
    let e : u32 = t - 96u;
    w[160u + e] = c[96u + e];
  }
  if (t >= 128u && t < 160u) {
    let e : u32 = t - 128u;
    w[192u + e] = w[0u + ix[0u + e]];
  }
  if (t >= 160u && t < 192u) {
    let e : u32 = t - 160u;
    w[224u + e] = w[0u + ix[32u + e]];
  }
}
