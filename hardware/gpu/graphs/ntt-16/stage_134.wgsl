// obend-emit-gpu: ntt-16, stage 134 of 398: 5 kernels, 10 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[390u + e] = select(w[389u + (e - 1u)], w[384u + e], e < 1u); }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[392u + e] = c[24u + e]; }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[394u + e] = c[26u + e]; }
  if (t >= 6u && t < 8u) { let e : u32 = t - 6u; w[396u + e] = c[28u + e]; }
  if (t >= 8u && t < 10u) { let e : u32 = t - 8u; w[398u + e] = c[30u + e]; }
}
