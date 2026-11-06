// obend-emit-gpu: glmul-256, stage 9 of 21: 3 kernels, 768 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 256u) { let e : u32 = t - 0u; w[5888u + e] = i64(u64(w[2816u + e]) >> u32(w[1024u + e])); }
  if (t >= 256u && t < 512u) { let e : u32 = t - 256u; w[6144u + e] = i64(u64(w[4352u + e]) >> u32(w[1024u + e])); }
  if (t >= 512u && t < 768u) { let e : u32 = t - 512u; w[6400u + e] = w[3072u + e] + w[5632u + e]; }
}
