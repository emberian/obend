// obend-emit-gpu: ntt-16, stage 354 of 398: 3 kernels, 12 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[1288u + e] = i64(u64(w[1240u + e]) >> u32(w[1212u + e])); }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[1292u + e] = i64(u64(w[1264u + e]) >> u32(w[1212u + e])); }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[1296u + e] = w[1244u + e] + w[1284u + e]; }
}
