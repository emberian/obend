// obend-emit-gpu: ntt-64, stage 1072 of 1670: 3 kernels, 6 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[5684u + e] = i64(u64(w[5660u + e]) >> u32(w[5646u + e])); }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[5686u + e] = i64(u64(w[5672u + e]) >> u32(w[5646u + e])); }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[5688u + e] = w[5662u + e] + w[5682u + e]; }
}
