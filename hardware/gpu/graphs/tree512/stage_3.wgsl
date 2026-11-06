// obend-emit-gpu: tree512, stage 3 of 9: 32 kernels, 32 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[960u + e] = w[896u + e] + w[897u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[961u + e] = w[898u + e] + w[899u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[962u + e] = w[900u + e] + w[901u + e]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[963u + e] = w[902u + e] + w[903u + e]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[964u + e] = w[904u + e] + w[905u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[965u + e] = w[906u + e] + w[907u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[966u + e] = w[908u + e] + w[909u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[967u + e] = w[910u + e] + w[911u + e]; }
  if (t >= 8u && t < 9u) { let e : u32 = t - 8u; w[968u + e] = w[912u + e] + w[913u + e]; }
  if (t >= 9u && t < 10u) { let e : u32 = t - 9u; w[969u + e] = w[914u + e] + w[915u + e]; }
  if (t >= 10u && t < 11u) { let e : u32 = t - 10u; w[970u + e] = w[916u + e] + w[917u + e]; }
  if (t >= 11u && t < 12u) { let e : u32 = t - 11u; w[971u + e] = w[918u + e] + w[919u + e]; }
  if (t >= 12u && t < 13u) { let e : u32 = t - 12u; w[972u + e] = w[920u + e] + w[921u + e]; }
  if (t >= 13u && t < 14u) { let e : u32 = t - 13u; w[973u + e] = w[922u + e] + w[923u + e]; }
  if (t >= 14u && t < 15u) { let e : u32 = t - 14u; w[974u + e] = w[924u + e] + w[925u + e]; }
  if (t >= 15u && t < 16u) { let e : u32 = t - 15u; w[975u + e] = w[926u + e] + w[927u + e]; }
  if (t >= 16u && t < 17u) { let e : u32 = t - 16u; w[976u + e] = w[928u + e] + w[929u + e]; }
  if (t >= 17u && t < 18u) { let e : u32 = t - 17u; w[977u + e] = w[930u + e] + w[931u + e]; }
  if (t >= 18u && t < 19u) { let e : u32 = t - 18u; w[978u + e] = w[932u + e] + w[933u + e]; }
  if (t >= 19u && t < 20u) { let e : u32 = t - 19u; w[979u + e] = w[934u + e] + w[935u + e]; }
  if (t >= 20u && t < 21u) { let e : u32 = t - 20u; w[980u + e] = w[936u + e] + w[937u + e]; }
  if (t >= 21u && t < 22u) { let e : u32 = t - 21u; w[981u + e] = w[938u + e] + w[939u + e]; }
  if (t >= 22u && t < 23u) { let e : u32 = t - 22u; w[982u + e] = w[940u + e] + w[941u + e]; }
  if (t >= 23u && t < 24u) { let e : u32 = t - 23u; w[983u + e] = w[942u + e] + w[943u + e]; }
  if (t >= 24u && t < 25u) { let e : u32 = t - 24u; w[984u + e] = w[944u + e] + w[945u + e]; }
  if (t >= 25u && t < 26u) { let e : u32 = t - 25u; w[985u + e] = w[946u + e] + w[947u + e]; }
  if (t >= 26u && t < 27u) { let e : u32 = t - 26u; w[986u + e] = w[948u + e] + w[949u + e]; }
  if (t >= 27u && t < 28u) { let e : u32 = t - 27u; w[987u + e] = w[950u + e] + w[951u + e]; }
  if (t >= 28u && t < 29u) { let e : u32 = t - 28u; w[988u + e] = w[952u + e] + w[953u + e]; }
  if (t >= 29u && t < 30u) { let e : u32 = t - 29u; w[989u + e] = w[954u + e] + w[955u + e]; }
  if (t >= 30u && t < 31u) { let e : u32 = t - 30u; w[990u + e] = w[956u + e] + w[957u + e]; }
  if (t >= 31u && t < 32u) { let e : u32 = t - 31u; w[991u + e] = w[958u + e] + w[959u + e]; }
}
