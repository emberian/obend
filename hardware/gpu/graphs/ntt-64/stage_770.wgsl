// obend-emit-gpu: ntt-64, stage 770 of 1670: 5 kernels, 40 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[3416u + e] = select(w[3412u + (e - 4u)], w[3392u + e], e < 4u); }
  if (t >= 8u && t < 16u) { let e : u32 = t - 8u; w[3424u + e] = c[224u + e]; }
  if (t >= 16u && t < 24u) { let e : u32 = t - 16u; w[3432u + e] = c[232u + e]; }
  if (t >= 24u && t < 32u) { let e : u32 = t - 24u; w[3440u + e] = c[240u + e]; }
  if (t >= 32u && t < 40u) { let e : u32 = t - 32u; w[3448u + e] = c[248u + e]; }
}
