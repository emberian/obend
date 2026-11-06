// obend-emit-gpu: ntt-64, stage 19 of 1670: 3 kernels, 3 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[220u + e] = w[219u + e] - w[217u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[221u + e] = select(i64(0), i64(1), u64(w[210u + e]) < u64(w[191u + e])); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[222u + e] = w[210u + e] - w[191u + e]; }
}
