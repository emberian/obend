// obend-emit-gpu: ntt-64, stage 1657 of 1670: 3 kernels, 96 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 32u) { let e : u32 = t - 0u; w[10368u + e] = w[10336u + e] - w[10272u + e]; }
  if (t >= 32u && t < 64u) { let e : u32 = t - 32u; w[10400u + e] = select(i64(0), i64(1), u64(w[10048u + e]) < u64(w[9440u + e])); }
  if (t >= 64u && t < 96u) { let e : u32 = t - 64u; w[10432u + e] = w[10048u + e] - w[9440u + e]; }
}
