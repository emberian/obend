// obend-emit-gpu: ntt-64, stage 1591 of 1670: 5 kernels, 40 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[8056u + e] = select(w[8052u + (e - 4u)], w[8032u + e], e < 4u); }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[8064u + e] = c[544u + e]; }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[8072u + e] = c[552u + e]; }
  if (t >= 24u && t < 32u) { let e : u32 = t - 24u; w[8080u + e] = c[560u + e]; }
  if (t >= 32u && t < 40u) { let e : u32 = t - 32u; w[8088u + e] = c[568u + e]; }
}
