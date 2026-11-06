// obend-emit-gpu: ntt-64, stage 834 of 1670: 2 kernels, 2 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[4850u + e] = w[4847u + e] | w[4849u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[4851u + e] = i64(u64(w[4839u + e]) >> u32(w[4833u + e])); }
}
