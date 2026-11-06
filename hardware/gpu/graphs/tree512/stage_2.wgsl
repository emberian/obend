// obend-emit-gpu: tree512, stage 2 of 9: 64 kernels, 64 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[896u + e] = w[768u + e] + w[769u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[897u + e] = w[770u + e] + w[771u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[898u + e] = w[772u + e] + w[773u + e]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[899u + e] = w[774u + e] + w[775u + e]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[900u + e] = w[776u + e] + w[777u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[901u + e] = w[778u + e] + w[779u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[902u + e] = w[780u + e] + w[781u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[903u + e] = w[782u + e] + w[783u + e]; }
  if (t >= 8u && t < 9u) { let e : u32 = t - 8u; w[904u + e] = w[784u + e] + w[785u + e]; }
  if (t >= 9u && t < 10u) { let e : u32 = t - 9u; w[905u + e] = w[786u + e] + w[787u + e]; }
  if (t >= 10u && t < 11u) { let e : u32 = t - 10u; w[906u + e] = w[788u + e] + w[789u + e]; }
  if (t >= 11u && t < 12u) { let e : u32 = t - 11u; w[907u + e] = w[790u + e] + w[791u + e]; }
  if (t >= 12u && t < 13u) { let e : u32 = t - 12u; w[908u + e] = w[792u + e] + w[793u + e]; }
  if (t >= 13u && t < 14u) { let e : u32 = t - 13u; w[909u + e] = w[794u + e] + w[795u + e]; }
  if (t >= 14u && t < 15u) { let e : u32 = t - 14u; w[910u + e] = w[796u + e] + w[797u + e]; }
  if (t >= 15u && t < 16u) { let e : u32 = t - 15u; w[911u + e] = w[798u + e] + w[799u + e]; }
  if (t >= 16u && t < 17u) { let e : u32 = t - 16u; w[912u + e] = w[800u + e] + w[801u + e]; }
  if (t >= 17u && t < 18u) { let e : u32 = t - 17u; w[913u + e] = w[802u + e] + w[803u + e]; }
  if (t >= 18u && t < 19u) { let e : u32 = t - 18u; w[914u + e] = w[804u + e] + w[805u + e]; }
  if (t >= 19u && t < 20u) { let e : u32 = t - 19u; w[915u + e] = w[806u + e] + w[807u + e]; }
  if (t >= 20u && t < 21u) { let e : u32 = t - 20u; w[916u + e] = w[808u + e] + w[809u + e]; }
  if (t >= 21u && t < 22u) { let e : u32 = t - 21u; w[917u + e] = w[810u + e] + w[811u + e]; }
  if (t >= 22u && t < 23u) { let e : u32 = t - 22u; w[918u + e] = w[812u + e] + w[813u + e]; }
  if (t >= 23u && t < 24u) { let e : u32 = t - 23u; w[919u + e] = w[814u + e] + w[815u + e]; }
  if (t >= 24u && t < 25u) { let e : u32 = t - 24u; w[920u + e] = w[816u + e] + w[817u + e]; }
  if (t >= 25u && t < 26u) { let e : u32 = t - 25u; w[921u + e] = w[818u + e] + w[819u + e]; }
  if (t >= 26u && t < 27u) { let e : u32 = t - 26u; w[922u + e] = w[820u + e] + w[821u + e]; }
  if (t >= 27u && t < 28u) { let e : u32 = t - 27u; w[923u + e] = w[822u + e] + w[823u + e]; }
  if (t >= 28u && t < 29u) { let e : u32 = t - 28u; w[924u + e] = w[824u + e] + w[825u + e]; }
  if (t >= 29u && t < 30u) { let e : u32 = t - 29u; w[925u + e] = w[826u + e] + w[827u + e]; }
  if (t >= 30u && t < 31u) { let e : u32 = t - 30u; w[926u + e] = w[828u + e] + w[829u + e]; }
  if (t >= 31u && t < 32u) { let e : u32 = t - 31u; w[927u + e] = w[830u + e] + w[831u + e]; }
  if (t >= 32u && t < 33u) { let e : u32 = t - 32u; w[928u + e] = w[832u + e] + w[833u + e]; }
  if (t >= 33u && t < 34u) { let e : u32 = t - 33u; w[929u + e] = w[834u + e] + w[835u + e]; }
  if (t >= 34u && t < 35u) { let e : u32 = t - 34u; w[930u + e] = w[836u + e] + w[837u + e]; }
  if (t >= 35u && t < 36u) { let e : u32 = t - 35u; w[931u + e] = w[838u + e] + w[839u + e]; }
  if (t >= 36u && t < 37u) { let e : u32 = t - 36u; w[932u + e] = w[840u + e] + w[841u + e]; }
  if (t >= 37u && t < 38u) { let e : u32 = t - 37u; w[933u + e] = w[842u + e] + w[843u + e]; }
  if (t >= 38u && t < 39u) { let e : u32 = t - 38u; w[934u + e] = w[844u + e] + w[845u + e]; }
  if (t >= 39u && t < 40u) { let e : u32 = t - 39u; w[935u + e] = w[846u + e] + w[847u + e]; }
  if (t >= 40u && t < 41u) { let e : u32 = t - 40u; w[936u + e] = w[848u + e] + w[849u + e]; }
  if (t >= 41u && t < 42u) { let e : u32 = t - 41u; w[937u + e] = w[850u + e] + w[851u + e]; }
  if (t >= 42u && t < 43u) { let e : u32 = t - 42u; w[938u + e] = w[852u + e] + w[853u + e]; }
  if (t >= 43u && t < 44u) { let e : u32 = t - 43u; w[939u + e] = w[854u + e] + w[855u + e]; }
  if (t >= 44u && t < 45u) { let e : u32 = t - 44u; w[940u + e] = w[856u + e] + w[857u + e]; }
  if (t >= 45u && t < 46u) { let e : u32 = t - 45u; w[941u + e] = w[858u + e] + w[859u + e]; }
  if (t >= 46u && t < 47u) { let e : u32 = t - 46u; w[942u + e] = w[860u + e] + w[861u + e]; }
  if (t >= 47u && t < 48u) { let e : u32 = t - 47u; w[943u + e] = w[862u + e] + w[863u + e]; }
  if (t >= 48u && t < 49u) { let e : u32 = t - 48u; w[944u + e] = w[864u + e] + w[865u + e]; }
  if (t >= 49u && t < 50u) { let e : u32 = t - 49u; w[945u + e] = w[866u + e] + w[867u + e]; }
  if (t >= 50u && t < 51u) { let e : u32 = t - 50u; w[946u + e] = w[868u + e] + w[869u + e]; }
  if (t >= 51u && t < 52u) { let e : u32 = t - 51u; w[947u + e] = w[870u + e] + w[871u + e]; }
  if (t >= 52u && t < 53u) { let e : u32 = t - 52u; w[948u + e] = w[872u + e] + w[873u + e]; }
  if (t >= 53u && t < 54u) { let e : u32 = t - 53u; w[949u + e] = w[874u + e] + w[875u + e]; }
  if (t >= 54u && t < 55u) { let e : u32 = t - 54u; w[950u + e] = w[876u + e] + w[877u + e]; }
  if (t >= 55u && t < 56u) { let e : u32 = t - 55u; w[951u + e] = w[878u + e] + w[879u + e]; }
  if (t >= 56u && t < 57u) { let e : u32 = t - 56u; w[952u + e] = w[880u + e] + w[881u + e]; }
  if (t >= 57u && t < 58u) { let e : u32 = t - 57u; w[953u + e] = w[882u + e] + w[883u + e]; }
  if (t >= 58u && t < 59u) { let e : u32 = t - 58u; w[954u + e] = w[884u + e] + w[885u + e]; }
  if (t >= 59u && t < 60u) { let e : u32 = t - 59u; w[955u + e] = w[886u + e] + w[887u + e]; }
  if (t >= 60u && t < 61u) { let e : u32 = t - 60u; w[956u + e] = w[888u + e] + w[889u + e]; }
  if (t >= 61u && t < 62u) { let e : u32 = t - 61u; w[957u + e] = w[890u + e] + w[891u + e]; }
  if (t >= 62u && t < 63u) { let e : u32 = t - 62u; w[958u + e] = w[892u + e] + w[893u + e]; }
  if (t >= 63u && t < 64u) { let e : u32 = t - 63u; w[959u + e] = w[894u + e] + w[895u + e]; }
}
