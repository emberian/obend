// obend-emit-gpu: ntt-64, stage 14 of 19: 2 kernels, 64 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 32u) {
    let e : u32 = t - 0u;
    let v224 : i64 = w[7264u + e] & w[96u + e];
    let v226 : i64 = w[7296u + e] & w[96u + e];
    let v228 : i64 = v224 * v226;
    let v237 : i64 = v228 & w[96u + e];
    let v232 : i64 = select(i64(0), i64(u64(v228) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v227 : i64 = select(i64(0), i64(u64(w[7296u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v229 : i64 = v224 * v227;
    let v233 : i64 = v229 & w[96u + e];
    let v235 : i64 = v232 + v233;
    let v225 : i64 = select(i64(0), i64(u64(w[7264u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v230 : i64 = v225 * v226;
    let v234 : i64 = v230 & w[96u + e];
    let v236 : i64 = v235 + v234;
    let v238 : i64 = v236 & w[96u + e];
    let v239 : i64 = select(i64(0), i64(u64(v238) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v240 : i64 = v237 | v239;
    let v251 : i64 = select(i64(0), i64(1), u64(v240) < u64(w[64u + e]));
    let v252 : i64 = v240 - w[64u + e];
    let v253 : i64 = select(v252, v240, v251 != i64(0));
    let v231 : i64 = v225 * v227;
    let v241 : i64 = select(i64(0), i64(u64(v229) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v244 : i64 = v231 + v241;
    let v242 : i64 = select(i64(0), i64(u64(v230) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v245 : i64 = v244 + v242;
    let v243 : i64 = select(i64(0), i64(u64(v236) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v246 : i64 = v245 + v243;
    let v247 : i64 = v246 & w[96u + e];
    let v249 : i64 = select(i64(0), i64(u64(v247) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v250 : i64 = v249 - v247;
    let v254 : i64 = w[64u + e] - v250;
    let v255 : i64 = select(i64(0), i64(1), u64(v253) < u64(v254));
    let v256 : i64 = v253 + v250;
    let v257 : i64 = v253 - v254;
    let v258 : i64 = select(v257, v256, v255 != i64(0));
    let v248 : i64 = select(i64(0), i64(u64(v246) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v259 : i64 = select(i64(0), i64(1), u64(v258) < u64(v248));
    let v260 : i64 = w[64u + e] - v248;
    let v261 : i64 = v260 + v258;
    let v262 : i64 = v258 - v248;
    let v263 : i64 = select(v262, v261, v259 != i64(0));
    let v264 : i64 = w[64u + e] - v263;
    let v265 : i64 = select(i64(0), i64(1), u64(w[7232u + e]) < u64(v264));
    let v266 : i64 = w[7232u + e] + v263;
    let v267 : i64 = w[7232u + e] - v264;
    let v268 : i64 = select(v267, v266, v265 != i64(0));
    w[8736u + e] = v268;
  }
  if (t >= 32u && t < 64u) {
    let e : u32 = t - 32u;
    let v224 : i64 = w[7264u + e] & w[96u + e];
    let v226 : i64 = w[7296u + e] & w[96u + e];
    let v228 : i64 = v224 * v226;
    let v237 : i64 = v228 & w[96u + e];
    let v232 : i64 = select(i64(0), i64(u64(v228) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v227 : i64 = select(i64(0), i64(u64(w[7296u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v229 : i64 = v224 * v227;
    let v233 : i64 = v229 & w[96u + e];
    let v235 : i64 = v232 + v233;
    let v225 : i64 = select(i64(0), i64(u64(w[7264u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v230 : i64 = v225 * v226;
    let v234 : i64 = v230 & w[96u + e];
    let v236 : i64 = v235 + v234;
    let v238 : i64 = v236 & w[96u + e];
    let v239 : i64 = select(i64(0), i64(u64(v238) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v240 : i64 = v237 | v239;
    let v251 : i64 = select(i64(0), i64(1), u64(v240) < u64(w[64u + e]));
    let v252 : i64 = v240 - w[64u + e];
    let v253 : i64 = select(v252, v240, v251 != i64(0));
    let v231 : i64 = v225 * v227;
    let v241 : i64 = select(i64(0), i64(u64(v229) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v244 : i64 = v231 + v241;
    let v242 : i64 = select(i64(0), i64(u64(v230) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v245 : i64 = v244 + v242;
    let v243 : i64 = select(i64(0), i64(u64(v236) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v246 : i64 = v245 + v243;
    let v247 : i64 = v246 & w[96u + e];
    let v249 : i64 = select(i64(0), i64(u64(v247) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v250 : i64 = v249 - v247;
    let v254 : i64 = w[64u + e] - v250;
    let v255 : i64 = select(i64(0), i64(1), u64(v253) < u64(v254));
    let v256 : i64 = v253 + v250;
    let v257 : i64 = v253 - v254;
    let v258 : i64 = select(v257, v256, v255 != i64(0));
    let v248 : i64 = select(i64(0), i64(u64(v246) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v259 : i64 = select(i64(0), i64(1), u64(v258) < u64(v248));
    let v260 : i64 = w[64u + e] - v248;
    let v261 : i64 = v260 + v258;
    let v262 : i64 = v258 - v248;
    let v263 : i64 = select(v262, v261, v259 != i64(0));
    let v269 : i64 = select(i64(0), i64(1), u64(w[7232u + e]) < u64(v263));
    let v270 : i64 = w[64u + e] - v263;
    let v271 : i64 = v270 + w[7232u + e];
    let v272 : i64 = w[7232u + e] - v263;
    let v273 : i64 = select(v272, v271, v269 != i64(0));
    w[8896u + e] = v273;
  }
}
