// obend-emit-gpu: ntt-64, stage 1617 of 1670: 5 kernels, 80 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 16u) { let e : u32 = t - 0u; w[8496u + e] = select(w[8488u + (e - 8u)], w[8448u + e], e < 8u); }
  if (t >= 16u && t < 32u) { let e : u32 = t - 16u; w[8512u + e] = c[576u + e]; }
  if (t >= 32u && t < 48u) { let e : u32 = t - 32u; w[8528u + e] = c[592u + e]; }
  if (t >= 48u && t < 64u) { let e : u32 = t - 48u; w[8544u + e] = c[608u + e]; }
  if (t >= 64u && t < 80u) { let e : u32 = t - 64u; w[8560u + e] = c[624u + e]; }
}
