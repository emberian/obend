// obend-emit-gpu: ntt-64, stage 1378 of 1670: 2 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[7134u + e] = w[7132u + e] + w[6972u + e]; }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[7136u + e] = w[6972u + e] - w[7118u + e]; }
}
