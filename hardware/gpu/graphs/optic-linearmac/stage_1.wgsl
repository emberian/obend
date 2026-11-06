// obend-emit-gpu: optic-linearmac, stage 1 of 2: 3 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[3u] = w[6u] + w[1u]; }
    case 1u: { w[4u] = c[1u] * w[2u]; }
    case 2u: { w[5u] = c[2u] * w[2u]; }
    default: { }
  }
}
