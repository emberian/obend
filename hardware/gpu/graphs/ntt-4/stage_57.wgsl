// obend-emit-gpu: ntt-4, stage 57 of 80: 2 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[152u + e] = w[144u + e] & w[128u + e]; }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[154u + e] = w[148u + e] + w[150u + e]; }
}
