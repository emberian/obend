// obend-emit-gpu: glmul-256, stage 1 of 21: 4 kernels, 1024 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 256u) { let e : u32 = t - 0u; w[1280u + e] = w[0u + e] & w[768u + e]; }
  if (t >= 256u && t < 512u) { let e : u32 = t - 256u; w[1536u + e] = i64(u64(w[0u + e]) >> u32(w[1024u + e])); }
  if (t >= 512u && t < 768u) { let e : u32 = t - 512u; w[1792u + e] = w[256u + e] & w[768u + e]; }
  if (t >= 768u && t < 1024u) { let e : u32 = t - 768u; w[2048u + e] = i64(u64(w[256u + e]) >> u32(w[1024u + e])); }
}
