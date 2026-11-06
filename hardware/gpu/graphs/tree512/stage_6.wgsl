// obend-emit-gpu: tree512, stage 6 of 9: 4 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[1016u] = w[1008u] + w[1009u]; }
    case 1u: { w[1017u] = w[1010u] + w[1011u]; }
    case 2u: { w[1018u] = w[1012u] + w[1013u]; }
    case 3u: { w[1019u] = w[1014u] + w[1015u]; }
    default: { }
  }
}
