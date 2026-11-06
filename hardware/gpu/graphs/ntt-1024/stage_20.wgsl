// obend-emit-gpu: ntt-1024, stage 20 of 31: 2 kernels, 1024 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 512u) {
    let e : u32 = t - 0u;
    let v332 : i64 = w[172544u + e] & w[1536u + e];
    let v334 : i64 = w[173056u + e] & w[1536u + e];
    let v336 : i64 = v332 * v334;
    let v345 : i64 = v336 & w[1536u + e];
    let v340 : i64 = select(i64(0), i64(u64(v336) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v335 : i64 = select(i64(0), i64(u64(w[173056u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v337 : i64 = v332 * v335;
    let v341 : i64 = v337 & w[1536u + e];
    let v343 : i64 = v340 + v341;
    let v333 : i64 = select(i64(0), i64(u64(w[172544u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v338 : i64 = v333 * v334;
    let v342 : i64 = v338 & w[1536u + e];
    let v344 : i64 = v343 + v342;
    let v346 : i64 = v344 & w[1536u + e];
    let v347 : i64 = select(i64(0), i64(u64(v346) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v348 : i64 = v345 | v347;
    let v359 : i64 = select(i64(0), i64(1), u64(v348) < u64(w[1024u + e]));
    let v360 : i64 = v348 - w[1024u + e];
    let v361 : i64 = select(v360, v348, v359 != i64(0));
    let v339 : i64 = v333 * v335;
    let v349 : i64 = select(i64(0), i64(u64(v337) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v352 : i64 = v339 + v349;
    let v350 : i64 = select(i64(0), i64(u64(v338) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v353 : i64 = v352 + v350;
    let v351 : i64 = select(i64(0), i64(u64(v344) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v354 : i64 = v353 + v351;
    let v355 : i64 = v354 & w[1536u + e];
    let v357 : i64 = select(i64(0), i64(u64(v355) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v358 : i64 = v357 - v355;
    let v362 : i64 = w[1024u + e] - v358;
    let v363 : i64 = select(i64(0), i64(1), u64(v361) < u64(v362));
    let v364 : i64 = v361 + v358;
    let v365 : i64 = v361 - v362;
    let v366 : i64 = select(v365, v364, v363 != i64(0));
    let v356 : i64 = select(i64(0), i64(u64(v354) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v367 : i64 = select(i64(0), i64(1), u64(v366) < u64(v356));
    let v368 : i64 = w[1024u + e] - v356;
    let v369 : i64 = v368 + v366;
    let v370 : i64 = v366 - v356;
    let v371 : i64 = select(v370, v369, v367 != i64(0));
    let v372 : i64 = w[1024u + e] - v371;
    let v373 : i64 = select(i64(0), i64(1), u64(w[172032u + e]) < u64(v372));
    let v374 : i64 = w[172032u + e] + v371;
    let v375 : i64 = w[172032u + e] - v372;
    let v376 : i64 = select(v375, v374, v373 != i64(0));
    w[196096u + e] = v376;
  }
  if (t >= 512u && t < 1024u) {
    let e : u32 = t - 512u;
    let v332 : i64 = w[172544u + e] & w[1536u + e];
    let v334 : i64 = w[173056u + e] & w[1536u + e];
    let v336 : i64 = v332 * v334;
    let v345 : i64 = v336 & w[1536u + e];
    let v340 : i64 = select(i64(0), i64(u64(v336) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v335 : i64 = select(i64(0), i64(u64(w[173056u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v337 : i64 = v332 * v335;
    let v341 : i64 = v337 & w[1536u + e];
    let v343 : i64 = v340 + v341;
    let v333 : i64 = select(i64(0), i64(u64(w[172544u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v338 : i64 = v333 * v334;
    let v342 : i64 = v338 & w[1536u + e];
    let v344 : i64 = v343 + v342;
    let v346 : i64 = v344 & w[1536u + e];
    let v347 : i64 = select(i64(0), i64(u64(v346) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v348 : i64 = v345 | v347;
    let v359 : i64 = select(i64(0), i64(1), u64(v348) < u64(w[1024u + e]));
    let v360 : i64 = v348 - w[1024u + e];
    let v361 : i64 = select(v360, v348, v359 != i64(0));
    let v339 : i64 = v333 * v335;
    let v349 : i64 = select(i64(0), i64(u64(v337) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v352 : i64 = v339 + v349;
    let v350 : i64 = select(i64(0), i64(u64(v338) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v353 : i64 = v352 + v350;
    let v351 : i64 = select(i64(0), i64(u64(v344) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v354 : i64 = v353 + v351;
    let v355 : i64 = v354 & w[1536u + e];
    let v357 : i64 = select(i64(0), i64(u64(v355) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v358 : i64 = v357 - v355;
    let v362 : i64 = w[1024u + e] - v358;
    let v363 : i64 = select(i64(0), i64(1), u64(v361) < u64(v362));
    let v364 : i64 = v361 + v358;
    let v365 : i64 = v361 - v362;
    let v366 : i64 = select(v365, v364, v363 != i64(0));
    let v356 : i64 = select(i64(0), i64(u64(v354) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v367 : i64 = select(i64(0), i64(1), u64(v366) < u64(v356));
    let v368 : i64 = w[1024u + e] - v356;
    let v369 : i64 = v368 + v366;
    let v370 : i64 = v366 - v356;
    let v371 : i64 = select(v370, v369, v367 != i64(0));
    let v377 : i64 = select(i64(0), i64(1), u64(w[172032u + e]) < u64(v371));
    let v378 : i64 = w[1024u + e] - v371;
    let v379 : i64 = v378 + w[172032u + e];
    let v380 : i64 = w[172032u + e] - v371;
    let v381 : i64 = select(v380, v379, v377 != i64(0));
    w[198656u + e] = v381;
  }
}
