// obend-emit-gpu: ntt-1024, stage 0 of 31: 6 kernels, 3072 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 512u) {
    let e : u32 = t - 0u;
    w[1024u + e] = c[0u + e];
  }
  if (t >= 512u && t < 1024u) {
    let e : u32 = t - 512u;
    w[1536u + e] = c[512u + e];
  }
  if (t >= 1024u && t < 1536u) {
    let e : u32 = t - 1024u;
    w[2048u + e] = c[1024u + e];
  }
  if (t >= 1536u && t < 2048u) {
    let e : u32 = t - 1536u;
    w[2560u + e] = c[1536u + e];
  }
  if (t >= 2048u && t < 2560u) {
    let e : u32 = t - 2048u;
    w[3072u + e] = w[0u + ix[0u + e]];
  }
  if (t >= 2560u && t < 3072u) {
    let e : u32 = t - 2560u;
    w[3584u + e] = w[0u + ix[512u + e]];
  }
}
