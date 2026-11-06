// obend-emit-gpu: ntt-16, stage 166 of 398: 2 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[572u + e] = w[536u + e] & w[512u + e]; }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[576u + e] = w[568u + e] & w[512u + e]; }
}
