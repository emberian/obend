// obend-emit-gpu: ntt-16, stage 59 of 398: 2 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[188u + e] = w[180u + e] & w[164u + e]; }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[190u + e] = w[184u + e] + w[186u + e]; }
}
