// obend-emit-gpu: ntt-1024, stage 12 of 31: 1 kernels, 1024 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1024u) {
    let e : u32 = t - 0u;
    w[114688u + e] = select(w[114176u + (e - 512u)], w[111616u + e], e < 512u);
  }
}
