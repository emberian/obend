// obend-emit-gpu: ntt-64, stage 321 of 1670: 5 kernels, 10 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[1230u + e] = select(w[1229u + (e - 1u)], w[1224u + e], e < 1u); }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[1232u + e] = c[72u + e]; }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[1234u + e] = c[74u + e]; }
  if (t >= 6u && t < 8u) { let e : u32 = t - 6u; w[1236u + e] = c[76u + e]; }
  if (t >= 8u && t < 10u) { let e : u32 = t - 8u; w[1238u + e] = c[78u + e]; }
}
