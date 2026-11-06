// obend-emit-gpu: ntt-64, stage 1643 of 1670: 5 kernels, 160 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 32u) { let e : u32 = t - 0u; w[9376u + e] = select(w[9360u + (e - 16u)], w[9280u + e], e < 16u); }
  if (t >= 32u && t < 64u) { let e : u32 = t - 32u; w[9408u + e] = c[640u + e]; }
  if (t >= 64u && t < 96u) { let e : u32 = t - 64u; w[9440u + e] = c[672u + e]; }
  if (t >= 96u && t < 128u) { let e : u32 = t - 96u; w[9472u + e] = c[704u + e]; }
  if (t >= 128u && t < 160u) { let e : u32 = t - 128u; w[9504u + e] = c[736u + e]; }
}
