// obend-emit-gpu: ntt-1024, stage 26 of 31: 2 kernels, 1024 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 512u) {
    let e : u32 = t - 0u;
    let v440 : i64 = w[228864u + e] & w[1536u + e];
    let v442 : i64 = w[229376u + e] & w[1536u + e];
    let v444 : i64 = v440 * v442;
    let v453 : i64 = v444 & w[1536u + e];
    let v448 : i64 = select(i64(0), i64(u64(v444) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v443 : i64 = select(i64(0), i64(u64(w[229376u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v445 : i64 = v440 * v443;
    let v449 : i64 = v445 & w[1536u + e];
    let v451 : i64 = v448 + v449;
    let v441 : i64 = select(i64(0), i64(u64(w[228864u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v446 : i64 = v441 * v442;
    let v450 : i64 = v446 & w[1536u + e];
    let v452 : i64 = v451 + v450;
    let v454 : i64 = v452 & w[1536u + e];
    let v455 : i64 = select(i64(0), i64(u64(v454) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v456 : i64 = v453 | v455;
    let v467 : i64 = select(i64(0), i64(1), u64(v456) < u64(w[1024u + e]));
    let v468 : i64 = v456 - w[1024u + e];
    let v469 : i64 = select(v468, v456, v467 != i64(0));
    let v447 : i64 = v441 * v443;
    let v457 : i64 = select(i64(0), i64(u64(v445) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v460 : i64 = v447 + v457;
    let v458 : i64 = select(i64(0), i64(u64(v446) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v461 : i64 = v460 + v458;
    let v459 : i64 = select(i64(0), i64(u64(v452) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v462 : i64 = v461 + v459;
    let v463 : i64 = v462 & w[1536u + e];
    let v465 : i64 = select(i64(0), i64(u64(v463) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v466 : i64 = v465 - v463;
    let v470 : i64 = w[1024u + e] - v466;
    let v471 : i64 = select(i64(0), i64(1), u64(v469) < u64(v470));
    let v472 : i64 = v469 + v466;
    let v473 : i64 = v469 - v470;
    let v474 : i64 = select(v473, v472, v471 != i64(0));
    let v464 : i64 = select(i64(0), i64(u64(v462) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v475 : i64 = select(i64(0), i64(1), u64(v474) < u64(v464));
    let v476 : i64 = w[1024u + e] - v464;
    let v477 : i64 = v476 + v474;
    let v478 : i64 = v474 - v464;
    let v479 : i64 = select(v478, v477, v475 != i64(0));
    let v480 : i64 = w[1024u + e] - v479;
    let v481 : i64 = select(i64(0), i64(1), u64(w[228352u + e]) < u64(v480));
    let v482 : i64 = w[228352u + e] + v479;
    let v483 : i64 = w[228352u + e] - v480;
    let v484 : i64 = select(v483, v482, v481 != i64(0));
    w[252416u + e] = v484;
  }
  if (t >= 512u && t < 1024u) {
    let e : u32 = t - 512u;
    let v440 : i64 = w[228864u + e] & w[1536u + e];
    let v442 : i64 = w[229376u + e] & w[1536u + e];
    let v444 : i64 = v440 * v442;
    let v453 : i64 = v444 & w[1536u + e];
    let v448 : i64 = select(i64(0), i64(u64(v444) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v443 : i64 = select(i64(0), i64(u64(w[229376u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v445 : i64 = v440 * v443;
    let v449 : i64 = v445 & w[1536u + e];
    let v451 : i64 = v448 + v449;
    let v441 : i64 = select(i64(0), i64(u64(w[228864u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v446 : i64 = v441 * v442;
    let v450 : i64 = v446 & w[1536u + e];
    let v452 : i64 = v451 + v450;
    let v454 : i64 = v452 & w[1536u + e];
    let v455 : i64 = select(i64(0), i64(u64(v454) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v456 : i64 = v453 | v455;
    let v467 : i64 = select(i64(0), i64(1), u64(v456) < u64(w[1024u + e]));
    let v468 : i64 = v456 - w[1024u + e];
    let v469 : i64 = select(v468, v456, v467 != i64(0));
    let v447 : i64 = v441 * v443;
    let v457 : i64 = select(i64(0), i64(u64(v445) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v460 : i64 = v447 + v457;
    let v458 : i64 = select(i64(0), i64(u64(v446) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v461 : i64 = v460 + v458;
    let v459 : i64 = select(i64(0), i64(u64(v452) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v462 : i64 = v461 + v459;
    let v463 : i64 = v462 & w[1536u + e];
    let v465 : i64 = select(i64(0), i64(u64(v463) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v466 : i64 = v465 - v463;
    let v470 : i64 = w[1024u + e] - v466;
    let v471 : i64 = select(i64(0), i64(1), u64(v469) < u64(v470));
    let v472 : i64 = v469 + v466;
    let v473 : i64 = v469 - v470;
    let v474 : i64 = select(v473, v472, v471 != i64(0));
    let v464 : i64 = select(i64(0), i64(u64(v462) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v475 : i64 = select(i64(0), i64(1), u64(v474) < u64(v464));
    let v476 : i64 = w[1024u + e] - v464;
    let v477 : i64 = v476 + v474;
    let v478 : i64 = v474 - v464;
    let v479 : i64 = select(v478, v477, v475 != i64(0));
    let v485 : i64 = select(i64(0), i64(1), u64(w[228352u + e]) < u64(v479));
    let v486 : i64 = w[1024u + e] - v479;
    let v487 : i64 = v486 + w[228352u + e];
    let v488 : i64 = w[228352u + e] - v479;
    let v489 : i64 = select(v488, v487, v485 != i64(0));
    w[254976u + e] = v489;
  }
}
