// obend-emit-gpu: ntt-1024, stage 29 of 31: 2 kernels, 1024 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 512u) {
    let e : u32 = t - 0u;
    let v494 : i64 = w[257024u + e] & w[1536u + e];
    let v496 : i64 = w[257536u + e] & w[1536u + e];
    let v498 : i64 = v494 * v496;
    let v507 : i64 = v498 & w[1536u + e];
    let v502 : i64 = i64(u64(v498) >> u32(w[2048u + e]));
    let v497 : i64 = i64(u64(w[257536u + e]) >> u32(w[2048u + e]));
    let v499 : i64 = v494 * v497;
    let v503 : i64 = v499 & w[1536u + e];
    let v505 : i64 = v502 + v503;
    let v495 : i64 = i64(u64(w[257024u + e]) >> u32(w[2048u + e]));
    let v500 : i64 = v495 * v496;
    let v504 : i64 = v500 & w[1536u + e];
    let v506 : i64 = v505 + v504;
    let v508 : i64 = v506 & w[1536u + e];
    let v509 : i64 = i64(u64(v508) << u32(w[2048u + e]));
    let v510 : i64 = v507 | v509;
    let v521 : i64 = select(i64(0), i64(1), u64(v510) < u64(w[1024u + e]));
    let v522 : i64 = v510 - w[1024u + e];
    let v523 : i64 = select(v522, v510, v521 != i64(0));
    let v501 : i64 = v495 * v497;
    let v511 : i64 = i64(u64(v499) >> u32(w[2048u + e]));
    let v514 : i64 = v501 + v511;
    let v512 : i64 = i64(u64(v500) >> u32(w[2048u + e]));
    let v515 : i64 = v514 + v512;
    let v513 : i64 = i64(u64(v506) >> u32(w[2048u + e]));
    let v516 : i64 = v515 + v513;
    let v517 : i64 = v516 & w[1536u + e];
    let v519 : i64 = i64(u64(v517) << u32(w[2048u + e]));
    let v520 : i64 = v519 - v517;
    let v524 : i64 = w[1024u + e] - v520;
    let v525 : i64 = select(i64(0), i64(1), u64(v523) < u64(v524));
    let v526 : i64 = v523 + v520;
    let v527 : i64 = v523 - v524;
    let v528 : i64 = select(v527, v526, v525 != i64(0));
    let v518 : i64 = i64(u64(v516) >> u32(w[2048u + e]));
    let v529 : i64 = select(i64(0), i64(1), u64(v528) < u64(v518));
    let v530 : i64 = w[1024u + e] - v518;
    let v531 : i64 = v530 + v528;
    let v532 : i64 = v528 - v518;
    let v533 : i64 = select(v532, v531, v529 != i64(0));
    let v534 : i64 = w[1024u + e] - v533;
    let v535 : i64 = select(i64(0), i64(1), u64(w[256512u + e]) < u64(v534));
    let v536 : i64 = w[256512u + e] + v533;
    let v537 : i64 = w[256512u + e] - v534;
    let v538 : i64 = select(v537, v536, v535 != i64(0));
    w[280576u + e] = v538;
  }
  if (t >= 512u && t < 1024u) {
    let e : u32 = t - 512u;
    let v494 : i64 = w[257024u + e] & w[1536u + e];
    let v496 : i64 = w[257536u + e] & w[1536u + e];
    let v498 : i64 = v494 * v496;
    let v507 : i64 = v498 & w[1536u + e];
    let v502 : i64 = i64(u64(v498) >> u32(w[2048u + e]));
    let v497 : i64 = i64(u64(w[257536u + e]) >> u32(w[2048u + e]));
    let v499 : i64 = v494 * v497;
    let v503 : i64 = v499 & w[1536u + e];
    let v505 : i64 = v502 + v503;
    let v495 : i64 = i64(u64(w[257024u + e]) >> u32(w[2048u + e]));
    let v500 : i64 = v495 * v496;
    let v504 : i64 = v500 & w[1536u + e];
    let v506 : i64 = v505 + v504;
    let v508 : i64 = v506 & w[1536u + e];
    let v509 : i64 = i64(u64(v508) << u32(w[2048u + e]));
    let v510 : i64 = v507 | v509;
    let v521 : i64 = select(i64(0), i64(1), u64(v510) < u64(w[1024u + e]));
    let v522 : i64 = v510 - w[1024u + e];
    let v523 : i64 = select(v522, v510, v521 != i64(0));
    let v501 : i64 = v495 * v497;
    let v511 : i64 = i64(u64(v499) >> u32(w[2048u + e]));
    let v514 : i64 = v501 + v511;
    let v512 : i64 = i64(u64(v500) >> u32(w[2048u + e]));
    let v515 : i64 = v514 + v512;
    let v513 : i64 = i64(u64(v506) >> u32(w[2048u + e]));
    let v516 : i64 = v515 + v513;
    let v517 : i64 = v516 & w[1536u + e];
    let v519 : i64 = i64(u64(v517) << u32(w[2048u + e]));
    let v520 : i64 = v519 - v517;
    let v524 : i64 = w[1024u + e] - v520;
    let v525 : i64 = select(i64(0), i64(1), u64(v523) < u64(v524));
    let v526 : i64 = v523 + v520;
    let v527 : i64 = v523 - v524;
    let v528 : i64 = select(v527, v526, v525 != i64(0));
    let v518 : i64 = i64(u64(v516) >> u32(w[2048u + e]));
    let v529 : i64 = select(i64(0), i64(1), u64(v528) < u64(v518));
    let v530 : i64 = w[1024u + e] - v518;
    let v531 : i64 = v530 + v528;
    let v532 : i64 = v528 - v518;
    let v533 : i64 = select(v532, v531, v529 != i64(0));
    let v539 : i64 = select(i64(0), i64(1), u64(w[256512u + e]) < u64(v533));
    let v540 : i64 = w[1024u + e] - v533;
    let v541 : i64 = v540 + w[256512u + e];
    let v542 : i64 = w[256512u + e] - v533;
    let v543 : i64 = select(v542, v541, v539 != i64(0));
    w[283136u + e] = v543;
  }
}
