// obend-emit-gpu: tree512, stage 4 of 9: 16 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[992u] = w[960u] + w[961u]; }
    case 1u: { w[993u] = w[962u] + w[963u]; }
    case 2u: { w[994u] = w[964u] + w[965u]; }
    case 3u: { w[995u] = w[966u] + w[967u]; }
    case 4u: { w[996u] = w[968u] + w[969u]; }
    case 5u: { w[997u] = w[970u] + w[971u]; }
    case 6u: { w[998u] = w[972u] + w[973u]; }
    case 7u: { w[999u] = w[974u] + w[975u]; }
    case 8u: { w[1000u] = w[976u] + w[977u]; }
    case 9u: { w[1001u] = w[978u] + w[979u]; }
    case 10u: { w[1002u] = w[980u] + w[981u]; }
    case 11u: { w[1003u] = w[982u] + w[983u]; }
    case 12u: { w[1004u] = w[984u] + w[985u]; }
    case 13u: { w[1005u] = w[986u] + w[987u]; }
    case 14u: { w[1006u] = w[988u] + w[989u]; }
    case 15u: { w[1007u] = w[990u] + w[991u]; }
    default: { }
  }
}
