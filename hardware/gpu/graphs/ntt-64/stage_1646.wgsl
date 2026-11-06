// obend-emit-gpu: ntt-64, stage 1646 of 1670: 4 kernels, 128 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 32u) { let e : u32 = t - 0u; w[9728u + e] = w[9568u + e] * w[9600u + e]; }
  if (t >= 32u && t < 64u) { let e : u32 = t - 32u; w[9760u + e] = w[9568u + e] * w[9632u + e]; }
  if (t >= 64u && t < 96u) { let e : u32 = t - 64u; w[9792u + e] = i64(u64(w[9664u + e]) >> u32(w[9504u + e])); }
  if (t >= 96u && t < 128u) { let e : u32 = t - 96u; w[9824u + e] = w[9696u + e] & w[9472u + e]; }
}
