// obend-emit-gpu: ntt-16, stage 11 of 13: 2 kernels, 16 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) {
    let e : u32 = t - 0u;
    let v170 : i64 = w[1376u + e] & w[24u + e];
    let v172 : i64 = w[1384u + e] & w[24u + e];
    let v174 : i64 = v170 * v172;
    let v183 : i64 = v174 & w[24u + e];
    let v178 : i64 = select(i64(0), i64(u64(v174) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v173 : i64 = select(i64(0), i64(u64(w[1384u + e]) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v175 : i64 = v170 * v173;
    let v179 : i64 = v175 & w[24u + e];
    let v181 : i64 = v178 + v179;
    let v171 : i64 = select(i64(0), i64(u64(w[1376u + e]) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v176 : i64 = v171 * v172;
    let v180 : i64 = v176 & w[24u + e];
    let v182 : i64 = v181 + v180;
    let v184 : i64 = v182 & w[24u + e];
    let v185 : i64 = select(i64(0), i64(u64(v184) << (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v186 : i64 = v183 | v185;
    let v197 : i64 = select(i64(0), i64(1), u64(v186) < u64(w[16u + e]));
    let v198 : i64 = v186 - w[16u + e];
    let v199 : i64 = select(v198, v186, v197 != i64(0));
    let v177 : i64 = v171 * v173;
    let v187 : i64 = select(i64(0), i64(u64(v175) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v190 : i64 = v177 + v187;
    let v188 : i64 = select(i64(0), i64(u64(v176) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v191 : i64 = v190 + v188;
    let v189 : i64 = select(i64(0), i64(u64(v182) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v192 : i64 = v191 + v189;
    let v193 : i64 = v192 & w[24u + e];
    let v195 : i64 = select(i64(0), i64(u64(v193) << (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v196 : i64 = v195 - v193;
    let v200 : i64 = w[16u + e] - v196;
    let v201 : i64 = select(i64(0), i64(1), u64(v199) < u64(v200));
    let v202 : i64 = v199 + v196;
    let v203 : i64 = v199 - v200;
    let v204 : i64 = select(v203, v202, v201 != i64(0));
    let v194 : i64 = select(i64(0), i64(u64(v192) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v205 : i64 = select(i64(0), i64(1), u64(v204) < u64(v194));
    let v206 : i64 = w[16u + e] - v194;
    let v207 : i64 = v206 + v204;
    let v208 : i64 = v204 - v194;
    let v209 : i64 = select(v208, v207, v205 != i64(0));
    let v210 : i64 = w[16u + e] - v209;
    let v211 : i64 = select(i64(0), i64(1), u64(w[1368u + e]) < u64(v210));
    let v212 : i64 = w[1368u + e] + v209;
    let v213 : i64 = w[1368u + e] - v210;
    let v214 : i64 = select(v213, v212, v211 != i64(0));
    w[1744u + e] = v214;
  }
  if (t >= 8u && t < 16u) {
    let e : u32 = t - 8u;
    let v170 : i64 = w[1376u + e] & w[24u + e];
    let v172 : i64 = w[1384u + e] & w[24u + e];
    let v174 : i64 = v170 * v172;
    let v183 : i64 = v174 & w[24u + e];
    let v178 : i64 = select(i64(0), i64(u64(v174) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v173 : i64 = select(i64(0), i64(u64(w[1384u + e]) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v175 : i64 = v170 * v173;
    let v179 : i64 = v175 & w[24u + e];
    let v181 : i64 = v178 + v179;
    let v171 : i64 = select(i64(0), i64(u64(w[1376u + e]) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v176 : i64 = v171 * v172;
    let v180 : i64 = v176 & w[24u + e];
    let v182 : i64 = v181 + v180;
    let v184 : i64 = v182 & w[24u + e];
    let v185 : i64 = select(i64(0), i64(u64(v184) << (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v186 : i64 = v183 | v185;
    let v197 : i64 = select(i64(0), i64(1), u64(v186) < u64(w[16u + e]));
    let v198 : i64 = v186 - w[16u + e];
    let v199 : i64 = select(v198, v186, v197 != i64(0));
    let v177 : i64 = v171 * v173;
    let v187 : i64 = select(i64(0), i64(u64(v175) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v190 : i64 = v177 + v187;
    let v188 : i64 = select(i64(0), i64(u64(v176) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v191 : i64 = v190 + v188;
    let v189 : i64 = select(i64(0), i64(u64(v182) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v192 : i64 = v191 + v189;
    let v193 : i64 = v192 & w[24u + e];
    let v195 : i64 = select(i64(0), i64(u64(v193) << (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v196 : i64 = v195 - v193;
    let v200 : i64 = w[16u + e] - v196;
    let v201 : i64 = select(i64(0), i64(1), u64(v199) < u64(v200));
    let v202 : i64 = v199 + v196;
    let v203 : i64 = v199 - v200;
    let v204 : i64 = select(v203, v202, v201 != i64(0));
    let v194 : i64 = select(i64(0), i64(u64(v192) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v205 : i64 = select(i64(0), i64(1), u64(v204) < u64(v194));
    let v206 : i64 = w[16u + e] - v194;
    let v207 : i64 = v206 + v204;
    let v208 : i64 = v204 - v194;
    let v209 : i64 = select(v208, v207, v205 != i64(0));
    let v215 : i64 = select(i64(0), i64(1), u64(w[1368u + e]) < u64(v209));
    let v216 : i64 = w[16u + e] - v209;
    let v217 : i64 = v216 + w[1368u + e];
    let v218 : i64 = w[1368u + e] - v209;
    let v219 : i64 = select(v218, v217, v215 != i64(0));
    w[1784u + e] = v219;
  }
}
