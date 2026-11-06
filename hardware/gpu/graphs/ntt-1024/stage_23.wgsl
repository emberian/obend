// obend-emit-gpu: ntt-1024, stage 23 of 31: 2 kernels, 1024 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 512u) {
    let e : u32 = t - 0u;
    let v386 : i64 = w[200704u + e] & w[1536u + e];
    let v388 : i64 = w[201216u + e] & w[1536u + e];
    let v390 : i64 = v386 * v388;
    let v399 : i64 = v390 & w[1536u + e];
    let v394 : i64 = i64(u64(v390) >> u32(w[2048u + e]));
    let v389 : i64 = i64(u64(w[201216u + e]) >> u32(w[2048u + e]));
    let v391 : i64 = v386 * v389;
    let v395 : i64 = v391 & w[1536u + e];
    let v397 : i64 = v394 + v395;
    let v387 : i64 = i64(u64(w[200704u + e]) >> u32(w[2048u + e]));
    let v392 : i64 = v387 * v388;
    let v396 : i64 = v392 & w[1536u + e];
    let v398 : i64 = v397 + v396;
    let v400 : i64 = v398 & w[1536u + e];
    let v401 : i64 = i64(u64(v400) << u32(w[2048u + e]));
    let v402 : i64 = v399 | v401;
    let v413 : i64 = select(i64(0), i64(1), u64(v402) < u64(w[1024u + e]));
    let v414 : i64 = v402 - w[1024u + e];
    let v415 : i64 = select(v414, v402, v413 != i64(0));
    let v393 : i64 = v387 * v389;
    let v403 : i64 = i64(u64(v391) >> u32(w[2048u + e]));
    let v406 : i64 = v393 + v403;
    let v404 : i64 = i64(u64(v392) >> u32(w[2048u + e]));
    let v407 : i64 = v406 + v404;
    let v405 : i64 = i64(u64(v398) >> u32(w[2048u + e]));
    let v408 : i64 = v407 + v405;
    let v409 : i64 = v408 & w[1536u + e];
    let v411 : i64 = i64(u64(v409) << u32(w[2048u + e]));
    let v412 : i64 = v411 - v409;
    let v416 : i64 = w[1024u + e] - v412;
    let v417 : i64 = select(i64(0), i64(1), u64(v415) < u64(v416));
    let v418 : i64 = v415 + v412;
    let v419 : i64 = v415 - v416;
    let v420 : i64 = select(v419, v418, v417 != i64(0));
    let v410 : i64 = i64(u64(v408) >> u32(w[2048u + e]));
    let v421 : i64 = select(i64(0), i64(1), u64(v420) < u64(v410));
    let v422 : i64 = w[1024u + e] - v410;
    let v423 : i64 = v422 + v420;
    let v424 : i64 = v420 - v410;
    let v425 : i64 = select(v424, v423, v421 != i64(0));
    let v426 : i64 = w[1024u + e] - v425;
    let v427 : i64 = select(i64(0), i64(1), u64(w[200192u + e]) < u64(v426));
    let v428 : i64 = w[200192u + e] + v425;
    let v429 : i64 = w[200192u + e] - v426;
    let v430 : i64 = select(v429, v428, v427 != i64(0));
    w[224256u + e] = v430;
  }
  if (t >= 512u && t < 1024u) {
    let e : u32 = t - 512u;
    let v386 : i64 = w[200704u + e] & w[1536u + e];
    let v388 : i64 = w[201216u + e] & w[1536u + e];
    let v390 : i64 = v386 * v388;
    let v399 : i64 = v390 & w[1536u + e];
    let v394 : i64 = i64(u64(v390) >> u32(w[2048u + e]));
    let v389 : i64 = i64(u64(w[201216u + e]) >> u32(w[2048u + e]));
    let v391 : i64 = v386 * v389;
    let v395 : i64 = v391 & w[1536u + e];
    let v397 : i64 = v394 + v395;
    let v387 : i64 = i64(u64(w[200704u + e]) >> u32(w[2048u + e]));
    let v392 : i64 = v387 * v388;
    let v396 : i64 = v392 & w[1536u + e];
    let v398 : i64 = v397 + v396;
    let v400 : i64 = v398 & w[1536u + e];
    let v401 : i64 = i64(u64(v400) << u32(w[2048u + e]));
    let v402 : i64 = v399 | v401;
    let v413 : i64 = select(i64(0), i64(1), u64(v402) < u64(w[1024u + e]));
    let v414 : i64 = v402 - w[1024u + e];
    let v415 : i64 = select(v414, v402, v413 != i64(0));
    let v393 : i64 = v387 * v389;
    let v403 : i64 = i64(u64(v391) >> u32(w[2048u + e]));
    let v406 : i64 = v393 + v403;
    let v404 : i64 = i64(u64(v392) >> u32(w[2048u + e]));
    let v407 : i64 = v406 + v404;
    let v405 : i64 = i64(u64(v398) >> u32(w[2048u + e]));
    let v408 : i64 = v407 + v405;
    let v409 : i64 = v408 & w[1536u + e];
    let v411 : i64 = i64(u64(v409) << u32(w[2048u + e]));
    let v412 : i64 = v411 - v409;
    let v416 : i64 = w[1024u + e] - v412;
    let v417 : i64 = select(i64(0), i64(1), u64(v415) < u64(v416));
    let v418 : i64 = v415 + v412;
    let v419 : i64 = v415 - v416;
    let v420 : i64 = select(v419, v418, v417 != i64(0));
    let v410 : i64 = i64(u64(v408) >> u32(w[2048u + e]));
    let v421 : i64 = select(i64(0), i64(1), u64(v420) < u64(v410));
    let v422 : i64 = w[1024u + e] - v410;
    let v423 : i64 = v422 + v420;
    let v424 : i64 = v420 - v410;
    let v425 : i64 = select(v424, v423, v421 != i64(0));
    let v431 : i64 = select(i64(0), i64(1), u64(w[200192u + e]) < u64(v425));
    let v432 : i64 = w[1024u + e] - v425;
    let v433 : i64 = v432 + w[200192u + e];
    let v434 : i64 = w[200192u + e] - v425;
    let v435 : i64 = select(v434, v433, v431 != i64(0));
    w[226816u + e] = v435;
  }
}
