// obend-emit-gpu: ntt-1024, stage 17 of 31: 2 kernels, 1024 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 512u) {
    let e : u32 = t - 0u;
    let v278 : i64 = w[144384u + e] & w[1536u + e];
    let v280 : i64 = w[144896u + e] & w[1536u + e];
    let v282 : i64 = v278 * v280;
    let v291 : i64 = v282 & w[1536u + e];
    let v286 : i64 = select(i64(0), i64(u64(v282) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v281 : i64 = select(i64(0), i64(u64(w[144896u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v283 : i64 = v278 * v281;
    let v287 : i64 = v283 & w[1536u + e];
    let v289 : i64 = v286 + v287;
    let v279 : i64 = select(i64(0), i64(u64(w[144384u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v284 : i64 = v279 * v280;
    let v288 : i64 = v284 & w[1536u + e];
    let v290 : i64 = v289 + v288;
    let v292 : i64 = v290 & w[1536u + e];
    let v293 : i64 = select(i64(0), i64(u64(v292) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v294 : i64 = v291 | v293;
    let v305 : i64 = select(i64(0), i64(1), u64(v294) < u64(w[1024u + e]));
    let v306 : i64 = v294 - w[1024u + e];
    let v307 : i64 = select(v306, v294, v305 != i64(0));
    let v285 : i64 = v279 * v281;
    let v295 : i64 = select(i64(0), i64(u64(v283) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v298 : i64 = v285 + v295;
    let v296 : i64 = select(i64(0), i64(u64(v284) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v299 : i64 = v298 + v296;
    let v297 : i64 = select(i64(0), i64(u64(v290) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v300 : i64 = v299 + v297;
    let v301 : i64 = v300 & w[1536u + e];
    let v303 : i64 = select(i64(0), i64(u64(v301) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v304 : i64 = v303 - v301;
    let v308 : i64 = w[1024u + e] - v304;
    let v309 : i64 = select(i64(0), i64(1), u64(v307) < u64(v308));
    let v310 : i64 = v307 + v304;
    let v311 : i64 = v307 - v308;
    let v312 : i64 = select(v311, v310, v309 != i64(0));
    let v302 : i64 = select(i64(0), i64(u64(v300) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v313 : i64 = select(i64(0), i64(1), u64(v312) < u64(v302));
    let v314 : i64 = w[1024u + e] - v302;
    let v315 : i64 = v314 + v312;
    let v316 : i64 = v312 - v302;
    let v317 : i64 = select(v316, v315, v313 != i64(0));
    let v318 : i64 = w[1024u + e] - v317;
    let v319 : i64 = select(i64(0), i64(1), u64(w[143872u + e]) < u64(v318));
    let v320 : i64 = w[143872u + e] + v317;
    let v321 : i64 = w[143872u + e] - v318;
    let v322 : i64 = select(v321, v320, v319 != i64(0));
    w[167936u + e] = v322;
  }
  if (t >= 512u && t < 1024u) {
    let e : u32 = t - 512u;
    let v278 : i64 = w[144384u + e] & w[1536u + e];
    let v280 : i64 = w[144896u + e] & w[1536u + e];
    let v282 : i64 = v278 * v280;
    let v291 : i64 = v282 & w[1536u + e];
    let v286 : i64 = select(i64(0), i64(u64(v282) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v281 : i64 = select(i64(0), i64(u64(w[144896u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v283 : i64 = v278 * v281;
    let v287 : i64 = v283 & w[1536u + e];
    let v289 : i64 = v286 + v287;
    let v279 : i64 = select(i64(0), i64(u64(w[144384u + e]) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v284 : i64 = v279 * v280;
    let v288 : i64 = v284 & w[1536u + e];
    let v290 : i64 = v289 + v288;
    let v292 : i64 = v290 & w[1536u + e];
    let v293 : i64 = select(i64(0), i64(u64(v292) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v294 : i64 = v291 | v293;
    let v305 : i64 = select(i64(0), i64(1), u64(v294) < u64(w[1024u + e]));
    let v306 : i64 = v294 - w[1024u + e];
    let v307 : i64 = select(v306, v294, v305 != i64(0));
    let v285 : i64 = v279 * v281;
    let v295 : i64 = select(i64(0), i64(u64(v283) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v298 : i64 = v285 + v295;
    let v296 : i64 = select(i64(0), i64(u64(v284) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v299 : i64 = v298 + v296;
    let v297 : i64 = select(i64(0), i64(u64(v290) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v300 : i64 = v299 + v297;
    let v301 : i64 = v300 & w[1536u + e];
    let v303 : i64 = select(i64(0), i64(u64(v301) << (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v304 : i64 = v303 - v301;
    let v308 : i64 = w[1024u + e] - v304;
    let v309 : i64 = select(i64(0), i64(1), u64(v307) < u64(v308));
    let v310 : i64 = v307 + v304;
    let v311 : i64 = v307 - v308;
    let v312 : i64 = select(v311, v310, v309 != i64(0));
    let v302 : i64 = select(i64(0), i64(u64(v300) >> (u32(w[2048u + e]) & 63u)), u64(w[2048u + e]) < u64(64));
    let v313 : i64 = select(i64(0), i64(1), u64(v312) < u64(v302));
    let v314 : i64 = w[1024u + e] - v302;
    let v315 : i64 = v314 + v312;
    let v316 : i64 = v312 - v302;
    let v317 : i64 = select(v316, v315, v313 != i64(0));
    let v323 : i64 = select(i64(0), i64(1), u64(w[143872u + e]) < u64(v317));
    let v324 : i64 = w[1024u + e] - v317;
    let v325 : i64 = v324 + w[143872u + e];
    let v326 : i64 = w[143872u + e] - v317;
    let v327 : i64 = select(v326, v325, v323 != i64(0));
    w[170496u + e] = v327;
  }
}
