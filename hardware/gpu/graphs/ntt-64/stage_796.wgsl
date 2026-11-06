// obend-emit-gpu: ntt-64, stage 796 of 1670: 5 kernels, 80 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 16u) { let e : u32 = t - 0u; w[3856u + e] = select(w[3848u + (e - 8u)], w[3808u + e], e < 8u); }
  if (t >= 16u && t < 32u) { let e : u32 = t - 16u; w[3872u + e] = c[256u + e]; }
  if (t >= 32u && t < 48u) { let e : u32 = t - 32u; w[3888u + e] = c[272u + e]; }
  if (t >= 48u && t < 64u) { let e : u32 = t - 48u; w[3904u + e] = c[288u + e]; }
  if (t >= 64u && t < 80u) { let e : u32 = t - 64u; w[3920u + e] = c[304u + e]; }
}
