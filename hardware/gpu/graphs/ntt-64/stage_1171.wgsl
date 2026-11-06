// obend-emit-gpu: ntt-64, stage 1171 of 1670: 4 kernels, 16 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) { let e : u32 = t - 0u; w[6024u + e] = w[6004u + e] * w[6008u + e]; }
  if (t >= 4u && t < 8u) { let e : u32 = t - 4u; w[6028u + e] = w[6004u + e] * w[6012u + e]; }
  if (t >= 8u && t < 12u) { let e : u32 = t - 8u; w[6032u + e] = i64(u64(w[6016u + e]) >> u32(w[5996u + e])); }
  if (t >= 12u && t < 16u) { let e : u32 = t - 12u; w[6036u + e] = w[6020u + e] & w[5992u + e]; }
}
