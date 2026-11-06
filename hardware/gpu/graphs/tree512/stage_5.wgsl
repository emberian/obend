// obend-emit-gpu: tree512, stage 5 of 9: 8 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[1008u] = w[992u] + w[993u]; }
    case 1u: { w[1009u] = w[994u] + w[995u]; }
    case 2u: { w[1010u] = w[996u] + w[997u]; }
    case 3u: { w[1011u] = w[998u] + w[999u]; }
    case 4u: { w[1012u] = w[1000u] + w[1001u]; }
    case 5u: { w[1013u] = w[1002u] + w[1003u]; }
    case 6u: { w[1014u] = w[1004u] + w[1005u]; }
    case 7u: { w[1015u] = w[1006u] + w[1007u]; }
    default: { }
  }
}
