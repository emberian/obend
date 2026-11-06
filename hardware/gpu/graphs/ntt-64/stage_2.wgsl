// obend-emit-gpu: ntt-64, stage 2 of 1670: 2 kernels, 24 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 16u) { let e : u32 = t - 0u; w[144u + e] = w[64u + ix[80u + e]]; }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[160u + e] = w[128u + ix[96u + e]]; }
}
