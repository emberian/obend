// obend-emit-gpu: ntt-64, stage 1406 of 1670: 2 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) { let e : u32 = t - 0u; w[7360u + e] = select(w[7356u + (e - 4u)], w[7336u + e], e < 4u); }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[7368u + e] = w[6664u + ix[360u + e]]; }
}
