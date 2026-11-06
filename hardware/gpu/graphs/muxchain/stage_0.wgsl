// obend-emit-gpu: muxchain, stage 0 of 3: 1 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[4u] = select(w[2u], w[1u], w[0u] != i64(0)); }
    default: { }
  }
}
