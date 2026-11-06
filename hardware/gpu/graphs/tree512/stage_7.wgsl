// obend-emit-gpu: tree512, stage 7 of 9: 2 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[1020u] = w[1016u] + w[1017u]; }
    case 1u: { w[1021u] = w[1018u] + w[1019u]; }
    default: { }
  }
}
