// obend-emit-gpu: ntt-16, stage 160 of 398: 5 kernels, 20 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[500u + e] = select(w[498u + (e - 2u)], w[488u + e], e < 2u); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[504u + e] = c[32u + e]; }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[508u + e] = c[36u + e]; }
  if (t >= 12u && t < 16u) { let e : u32 = t - 12u; w[512u + e] = c[40u + e]; }
  if (t >= 16u && t < 20u) { let e : u32 = t - 16u; w[516u + e] = c[44u + e]; }
}
