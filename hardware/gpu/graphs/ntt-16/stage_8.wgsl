// obend-emit-gpu: ntt-16, stage 8 of 13: 2 kernels, 16 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 8u) {
    let e : u32 = t - 0u;
    let v116 : i64 = w[936u + e] & w[24u + e];
    let v118 : i64 = w[944u + e] & w[24u + e];
    let v120 : i64 = v116 * v118;
    let v129 : i64 = v120 & w[24u + e];
    let v124 : i64 = select(i64(0), i64(u64(v120) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v119 : i64 = select(i64(0), i64(u64(w[944u + e]) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v121 : i64 = v116 * v119;
    let v125 : i64 = v121 & w[24u + e];
    let v127 : i64 = v124 + v125;
    let v117 : i64 = select(i64(0), i64(u64(w[936u + e]) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v122 : i64 = v117 * v118;
    let v126 : i64 = v122 & w[24u + e];
    let v128 : i64 = v127 + v126;
    let v130 : i64 = v128 & w[24u + e];
    let v131 : i64 = select(i64(0), i64(u64(v130) << (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v132 : i64 = v129 | v131;
    let v143 : i64 = select(i64(0), i64(1), u64(v132) < u64(w[16u + e]));
    let v144 : i64 = v132 - w[16u + e];
    let v145 : i64 = select(v144, v132, v143 != i64(0));
    let v123 : i64 = v117 * v119;
    let v133 : i64 = select(i64(0), i64(u64(v121) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v136 : i64 = v123 + v133;
    let v134 : i64 = select(i64(0), i64(u64(v122) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v137 : i64 = v136 + v134;
    let v135 : i64 = select(i64(0), i64(u64(v128) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v138 : i64 = v137 + v135;
    let v139 : i64 = v138 & w[24u + e];
    let v141 : i64 = select(i64(0), i64(u64(v139) << (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v142 : i64 = v141 - v139;
    let v146 : i64 = w[16u + e] - v142;
    let v147 : i64 = select(i64(0), i64(1), u64(v145) < u64(v146));
    let v148 : i64 = v145 + v142;
    let v149 : i64 = v145 - v146;
    let v150 : i64 = select(v149, v148, v147 != i64(0));
    let v140 : i64 = select(i64(0), i64(u64(v138) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v151 : i64 = select(i64(0), i64(1), u64(v150) < u64(v140));
    let v152 : i64 = w[16u + e] - v140;
    let v153 : i64 = v152 + v150;
    let v154 : i64 = v150 - v140;
    let v155 : i64 = select(v154, v153, v151 != i64(0));
    let v156 : i64 = w[16u + e] - v155;
    let v157 : i64 = select(i64(0), i64(1), u64(w[928u + e]) < u64(v156));
    let v158 : i64 = w[928u + e] + v155;
    let v159 : i64 = w[928u + e] - v156;
    let v160 : i64 = select(v159, v158, v157 != i64(0));
    w[1304u + e] = v160;
  }
  if (t >= 8u && t < 16u) {
    let e : u32 = t - 8u;
    let v116 : i64 = w[936u + e] & w[24u + e];
    let v118 : i64 = w[944u + e] & w[24u + e];
    let v120 : i64 = v116 * v118;
    let v129 : i64 = v120 & w[24u + e];
    let v124 : i64 = select(i64(0), i64(u64(v120) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v119 : i64 = select(i64(0), i64(u64(w[944u + e]) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v121 : i64 = v116 * v119;
    let v125 : i64 = v121 & w[24u + e];
    let v127 : i64 = v124 + v125;
    let v117 : i64 = select(i64(0), i64(u64(w[936u + e]) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v122 : i64 = v117 * v118;
    let v126 : i64 = v122 & w[24u + e];
    let v128 : i64 = v127 + v126;
    let v130 : i64 = v128 & w[24u + e];
    let v131 : i64 = select(i64(0), i64(u64(v130) << (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v132 : i64 = v129 | v131;
    let v143 : i64 = select(i64(0), i64(1), u64(v132) < u64(w[16u + e]));
    let v144 : i64 = v132 - w[16u + e];
    let v145 : i64 = select(v144, v132, v143 != i64(0));
    let v123 : i64 = v117 * v119;
    let v133 : i64 = select(i64(0), i64(u64(v121) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v136 : i64 = v123 + v133;
    let v134 : i64 = select(i64(0), i64(u64(v122) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v137 : i64 = v136 + v134;
    let v135 : i64 = select(i64(0), i64(u64(v128) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v138 : i64 = v137 + v135;
    let v139 : i64 = v138 & w[24u + e];
    let v141 : i64 = select(i64(0), i64(u64(v139) << (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v142 : i64 = v141 - v139;
    let v146 : i64 = w[16u + e] - v142;
    let v147 : i64 = select(i64(0), i64(1), u64(v145) < u64(v146));
    let v148 : i64 = v145 + v142;
    let v149 : i64 = v145 - v146;
    let v150 : i64 = select(v149, v148, v147 != i64(0));
    let v140 : i64 = select(i64(0), i64(u64(v138) >> (u32(w[32u + e]) & 63u)), u64(w[32u + e]) < u64(64));
    let v151 : i64 = select(i64(0), i64(1), u64(v150) < u64(v140));
    let v152 : i64 = w[16u + e] - v140;
    let v153 : i64 = v152 + v150;
    let v154 : i64 = v150 - v140;
    let v155 : i64 = select(v154, v153, v151 != i64(0));
    let v161 : i64 = select(i64(0), i64(1), u64(w[928u + e]) < u64(v155));
    let v162 : i64 = w[16u + e] - v155;
    let v163 : i64 = v162 + w[928u + e];
    let v164 : i64 = w[928u + e] - v155;
    let v165 : i64 = select(v164, v163, v161 != i64(0));
    w[1344u + e] = v165;
  }
}
