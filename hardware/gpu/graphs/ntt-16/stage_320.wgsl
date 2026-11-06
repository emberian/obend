// obend-emit-gpu: ntt-16, stage 320 of 398: 4 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 2u) { let e : u32 = t - 0u; w[1096u + e] = w[1086u + e] & w[1092u + e]; }
  if (t >= 2u && t < 4u) { let e : u32 = t - 2u; w[1098u + e] = i64(u64(w[1086u + e]) >> u32(w[1094u + e])); }
  if (t >= 4u && t < 6u) { let e : u32 = t - 4u; w[1100u + e] = w[1088u + e] & w[1092u + e]; }
  if (t >= 6u && t < 8u) { let e : u32 = t - 6u; w[1102u + e] = i64(u64(w[1088u + e]) >> u32(w[1094u + e])); }
}
