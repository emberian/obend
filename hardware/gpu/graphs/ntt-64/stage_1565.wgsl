// obend-emit-gpu: ntt-64, stage 1565 of 1670: 5 kernels, 20 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[7836u + e] = select(w[7834u + (e - 2u)], w[7824u + e], e < 2u); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[7840u + e] = c[528u + e]; }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[7844u + e] = c[532u + e]; }
  if (t >= 12u && t < 16u) { let e : u32 = t - 12u; w[7848u + e] = c[536u + e]; }
  if (t >= 16u && t < 20u) { let e : u32 = t - 16u; w[7852u + e] = c[540u + e]; }
}
