// obend-emit-gpu: tree512, stage 3 of 9: 32 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[960u] = w[896u] + w[897u]; }
    case 1u: { w[961u] = w[898u] + w[899u]; }
    case 2u: { w[962u] = w[900u] + w[901u]; }
    case 3u: { w[963u] = w[902u] + w[903u]; }
    case 4u: { w[964u] = w[904u] + w[905u]; }
    case 5u: { w[965u] = w[906u] + w[907u]; }
    case 6u: { w[966u] = w[908u] + w[909u]; }
    case 7u: { w[967u] = w[910u] + w[911u]; }
    case 8u: { w[968u] = w[912u] + w[913u]; }
    case 9u: { w[969u] = w[914u] + w[915u]; }
    case 10u: { w[970u] = w[916u] + w[917u]; }
    case 11u: { w[971u] = w[918u] + w[919u]; }
    case 12u: { w[972u] = w[920u] + w[921u]; }
    case 13u: { w[973u] = w[922u] + w[923u]; }
    case 14u: { w[974u] = w[924u] + w[925u]; }
    case 15u: { w[975u] = w[926u] + w[927u]; }
    case 16u: { w[976u] = w[928u] + w[929u]; }
    case 17u: { w[977u] = w[930u] + w[931u]; }
    case 18u: { w[978u] = w[932u] + w[933u]; }
    case 19u: { w[979u] = w[934u] + w[935u]; }
    case 20u: { w[980u] = w[936u] + w[937u]; }
    case 21u: { w[981u] = w[938u] + w[939u]; }
    case 22u: { w[982u] = w[940u] + w[941u]; }
    case 23u: { w[983u] = w[942u] + w[943u]; }
    case 24u: { w[984u] = w[944u] + w[945u]; }
    case 25u: { w[985u] = w[946u] + w[947u]; }
    case 26u: { w[986u] = w[948u] + w[949u]; }
    case 27u: { w[987u] = w[950u] + w[951u]; }
    case 28u: { w[988u] = w[952u] + w[953u]; }
    case 29u: { w[989u] = w[954u] + w[955u]; }
    case 30u: { w[990u] = w[956u] + w[957u]; }
    case 31u: { w[991u] = w[958u] + w[959u]; }
    default: { }
  }
}
