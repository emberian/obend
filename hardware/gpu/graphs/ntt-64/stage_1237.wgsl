// obend-emit-gpu: ntt-64, stage 1237 of 1670: 3 kernels, 3 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[6716u + e] = w[6715u + e] - w[6713u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[6717u + e] = select(i64(0), i64(1), u64(w[6706u + e]) < u64(w[6687u + e])); }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[6718u + e] = w[6706u + e] - w[6687u + e]; }
}
