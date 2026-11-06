// obend-emit-gpu: ntt-64, stage 1194 of 1670: 5 kernels, 40 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[6200u + e] = select(w[6196u + (e - 4u)], w[6176u + e], e < 4u); }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[6208u + e] = c[416u + e]; }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[6216u + e] = c[424u + e]; }
  if (t >= 24u && t < 32u) { let e : u32 = t - 24u; w[6224u + e] = c[432u + e]; }
  if (t >= 32u && t < 40u) { let e : u32 = t - 32u; w[6232u + e] = c[440u + e]; }
}
