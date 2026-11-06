// obend-emit-gpu: tree512, stage 2 of 9: 64 threads, one hyperedge each.
// Generated from Obend.Hardware.Gpu.lowerHypergraphToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  switch gid.x {
    case 0u: { w[896u] = w[768u] + w[769u]; }
    case 1u: { w[897u] = w[770u] + w[771u]; }
    case 2u: { w[898u] = w[772u] + w[773u]; }
    case 3u: { w[899u] = w[774u] + w[775u]; }
    case 4u: { w[900u] = w[776u] + w[777u]; }
    case 5u: { w[901u] = w[778u] + w[779u]; }
    case 6u: { w[902u] = w[780u] + w[781u]; }
    case 7u: { w[903u] = w[782u] + w[783u]; }
    case 8u: { w[904u] = w[784u] + w[785u]; }
    case 9u: { w[905u] = w[786u] + w[787u]; }
    case 10u: { w[906u] = w[788u] + w[789u]; }
    case 11u: { w[907u] = w[790u] + w[791u]; }
    case 12u: { w[908u] = w[792u] + w[793u]; }
    case 13u: { w[909u] = w[794u] + w[795u]; }
    case 14u: { w[910u] = w[796u] + w[797u]; }
    case 15u: { w[911u] = w[798u] + w[799u]; }
    case 16u: { w[912u] = w[800u] + w[801u]; }
    case 17u: { w[913u] = w[802u] + w[803u]; }
    case 18u: { w[914u] = w[804u] + w[805u]; }
    case 19u: { w[915u] = w[806u] + w[807u]; }
    case 20u: { w[916u] = w[808u] + w[809u]; }
    case 21u: { w[917u] = w[810u] + w[811u]; }
    case 22u: { w[918u] = w[812u] + w[813u]; }
    case 23u: { w[919u] = w[814u] + w[815u]; }
    case 24u: { w[920u] = w[816u] + w[817u]; }
    case 25u: { w[921u] = w[818u] + w[819u]; }
    case 26u: { w[922u] = w[820u] + w[821u]; }
    case 27u: { w[923u] = w[822u] + w[823u]; }
    case 28u: { w[924u] = w[824u] + w[825u]; }
    case 29u: { w[925u] = w[826u] + w[827u]; }
    case 30u: { w[926u] = w[828u] + w[829u]; }
    case 31u: { w[927u] = w[830u] + w[831u]; }
    case 32u: { w[928u] = w[832u] + w[833u]; }
    case 33u: { w[929u] = w[834u] + w[835u]; }
    case 34u: { w[930u] = w[836u] + w[837u]; }
    case 35u: { w[931u] = w[838u] + w[839u]; }
    case 36u: { w[932u] = w[840u] + w[841u]; }
    case 37u: { w[933u] = w[842u] + w[843u]; }
    case 38u: { w[934u] = w[844u] + w[845u]; }
    case 39u: { w[935u] = w[846u] + w[847u]; }
    case 40u: { w[936u] = w[848u] + w[849u]; }
    case 41u: { w[937u] = w[850u] + w[851u]; }
    case 42u: { w[938u] = w[852u] + w[853u]; }
    case 43u: { w[939u] = w[854u] + w[855u]; }
    case 44u: { w[940u] = w[856u] + w[857u]; }
    case 45u: { w[941u] = w[858u] + w[859u]; }
    case 46u: { w[942u] = w[860u] + w[861u]; }
    case 47u: { w[943u] = w[862u] + w[863u]; }
    case 48u: { w[944u] = w[864u] + w[865u]; }
    case 49u: { w[945u] = w[866u] + w[867u]; }
    case 50u: { w[946u] = w[868u] + w[869u]; }
    case 51u: { w[947u] = w[870u] + w[871u]; }
    case 52u: { w[948u] = w[872u] + w[873u]; }
    case 53u: { w[949u] = w[874u] + w[875u]; }
    case 54u: { w[950u] = w[876u] + w[877u]; }
    case 55u: { w[951u] = w[878u] + w[879u]; }
    case 56u: { w[952u] = w[880u] + w[881u]; }
    case 57u: { w[953u] = w[882u] + w[883u]; }
    case 58u: { w[954u] = w[884u] + w[885u]; }
    case 59u: { w[955u] = w[886u] + w[887u]; }
    case 60u: { w[956u] = w[888u] + w[889u]; }
    case 61u: { w[957u] = w[890u] + w[891u]; }
    case 62u: { w[958u] = w[892u] + w[893u]; }
    case 63u: { w[959u] = w[894u] + w[895u]; }
    default: { }
  }
}
