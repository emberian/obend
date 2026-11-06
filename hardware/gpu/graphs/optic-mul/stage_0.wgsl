// obend-emit-gpu: optic-mul, stage 0 of 1: 3 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[3u] = w[0u] * w[1u]; }
    case 1u: { w[4u] = w[1u] * w[2u]; }
    case 2u: { w[5u] = w[0u] * w[2u]; }
    default: { }
  }
}
