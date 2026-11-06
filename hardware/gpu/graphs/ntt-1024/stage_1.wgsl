// obend-emit-gpu: ntt-1024, stage 1 of 31: 10 kernels, 5120 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 512u) {
    let e : u32 = t - 0u;
    w[4096u + e] = w[2560u + ix[1024u + e]];
  }
  if (t >= 512u && t < 1024u) {
    let e : u32 = t - 512u;
    w[32256u + e] = w[2560u + ix[1536u + e]];
  }
  if (t >= 1024u && t < 1536u) {
    let e : u32 = t - 1024u;
    w[60416u + e] = w[2560u + ix[2048u + e]];
  }
  if (t >= 1536u && t < 2048u) {
    let e : u32 = t - 1536u;
    w[88576u + e] = w[2560u + ix[2560u + e]];
  }
  if (t >= 2048u && t < 2560u) {
    let e : u32 = t - 2048u;
    w[116736u + e] = w[2560u + ix[3072u + e]];
  }
  if (t >= 2560u && t < 3072u) {
    let e : u32 = t - 2560u;
    w[144896u + e] = w[2560u + ix[3584u + e]];
  }
  if (t >= 3072u && t < 3584u) {
    let e : u32 = t - 3072u;
    w[173056u + e] = w[2560u + ix[4096u + e]];
  }
  if (t >= 3584u && t < 4096u) {
    let e : u32 = t - 3584u;
    w[201216u + e] = w[2560u + ix[4608u + e]];
  }
  if (t >= 4096u && t < 4608u) {
    let e : u32 = t - 4096u;
    w[229376u + e] = w[2560u + ix[5120u + e]];
  }
  if (t >= 4608u && t < 5120u) {
    let e : u32 = t - 4608u;
    w[257536u + e] = w[2560u + ix[5632u + e]];
  }
}
