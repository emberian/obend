// obend-emit-gpu: ntt-16, stage 375 of 398: 2 kernels, 16 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[1536u + e] = w[1504u + e] & w[1440u + e]; }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[1544u + e] = w[1520u + e] + w[1528u + e]; }
}
