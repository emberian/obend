// obend-emit-gpu: ntt-64, stage 1089 of 1670: 2 kernels, 6 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[5748u + e] = select(w[5746u + (e - 2u)], w[5736u + e], e < 2u); }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[5752u + e] = w[5516u + ix[312u + e]]; }
}
