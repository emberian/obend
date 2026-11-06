// obend-emit-gpu: ntt-64, stage 5 of 19: 2 kernels, 64 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 32u) {
    let e : u32 = t - 0u;
    let v62 : i64 = w[1984u + e] & w[96u + e];
    let v64 : i64 = w[2016u + e] & w[96u + e];
    let v66 : i64 = v62 * v64;
    let v75 : i64 = v66 & w[96u + e];
    let v70 : i64 = select(i64(0), i64(u64(v66) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v65 : i64 = select(i64(0), i64(u64(w[2016u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v67 : i64 = v62 * v65;
    let v71 : i64 = v67 & w[96u + e];
    let v73 : i64 = v70 + v71;
    let v63 : i64 = select(i64(0), i64(u64(w[1984u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v68 : i64 = v63 * v64;
    let v72 : i64 = v68 & w[96u + e];
    let v74 : i64 = v73 + v72;
    let v76 : i64 = v74 & w[96u + e];
    let v77 : i64 = select(i64(0), i64(u64(v76) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v78 : i64 = v75 | v77;
    let v89 : i64 = select(i64(0), i64(1), u64(v78) < u64(w[64u + e]));
    let v90 : i64 = v78 - w[64u + e];
    let v91 : i64 = select(v90, v78, v89 != i64(0));
    let v69 : i64 = v63 * v65;
    let v79 : i64 = select(i64(0), i64(u64(v67) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v82 : i64 = v69 + v79;
    let v80 : i64 = select(i64(0), i64(u64(v68) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v83 : i64 = v82 + v80;
    let v81 : i64 = select(i64(0), i64(u64(v74) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v84 : i64 = v83 + v81;
    let v85 : i64 = v84 & w[96u + e];
    let v87 : i64 = select(i64(0), i64(u64(v85) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v88 : i64 = v87 - v85;
    let v92 : i64 = w[64u + e] - v88;
    let v93 : i64 = select(i64(0), i64(1), u64(v91) < u64(v92));
    let v94 : i64 = v91 + v88;
    let v95 : i64 = v91 - v92;
    let v96 : i64 = select(v95, v94, v93 != i64(0));
    let v86 : i64 = select(i64(0), i64(u64(v84) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v97 : i64 = select(i64(0), i64(1), u64(v96) < u64(v86));
    let v98 : i64 = w[64u + e] - v86;
    let v99 : i64 = v98 + v96;
    let v100 : i64 = v96 - v86;
    let v101 : i64 = select(v100, v99, v97 != i64(0));
    let v102 : i64 = w[64u + e] - v101;
    let v103 : i64 = select(i64(0), i64(1), u64(w[1952u + e]) < u64(v102));
    let v104 : i64 = w[1952u + e] + v101;
    let v105 : i64 = w[1952u + e] - v102;
    let v106 : i64 = select(v105, v104, v103 != i64(0));
    w[3456u + e] = v106;
  }
  if (t >= 32u && t < 64u) {
    let e : u32 = t - 32u;
    let v62 : i64 = w[1984u + e] & w[96u + e];
    let v64 : i64 = w[2016u + e] & w[96u + e];
    let v66 : i64 = v62 * v64;
    let v75 : i64 = v66 & w[96u + e];
    let v70 : i64 = select(i64(0), i64(u64(v66) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v65 : i64 = select(i64(0), i64(u64(w[2016u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v67 : i64 = v62 * v65;
    let v71 : i64 = v67 & w[96u + e];
    let v73 : i64 = v70 + v71;
    let v63 : i64 = select(i64(0), i64(u64(w[1984u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v68 : i64 = v63 * v64;
    let v72 : i64 = v68 & w[96u + e];
    let v74 : i64 = v73 + v72;
    let v76 : i64 = v74 & w[96u + e];
    let v77 : i64 = select(i64(0), i64(u64(v76) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v78 : i64 = v75 | v77;
    let v89 : i64 = select(i64(0), i64(1), u64(v78) < u64(w[64u + e]));
    let v90 : i64 = v78 - w[64u + e];
    let v91 : i64 = select(v90, v78, v89 != i64(0));
    let v69 : i64 = v63 * v65;
    let v79 : i64 = select(i64(0), i64(u64(v67) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v82 : i64 = v69 + v79;
    let v80 : i64 = select(i64(0), i64(u64(v68) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v83 : i64 = v82 + v80;
    let v81 : i64 = select(i64(0), i64(u64(v74) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v84 : i64 = v83 + v81;
    let v85 : i64 = v84 & w[96u + e];
    let v87 : i64 = select(i64(0), i64(u64(v85) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v88 : i64 = v87 - v85;
    let v92 : i64 = w[64u + e] - v88;
    let v93 : i64 = select(i64(0), i64(1), u64(v91) < u64(v92));
    let v94 : i64 = v91 + v88;
    let v95 : i64 = v91 - v92;
    let v96 : i64 = select(v95, v94, v93 != i64(0));
    let v86 : i64 = select(i64(0), i64(u64(v84) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v97 : i64 = select(i64(0), i64(1), u64(v96) < u64(v86));
    let v98 : i64 = w[64u + e] - v86;
    let v99 : i64 = v98 + v96;
    let v100 : i64 = v96 - v86;
    let v101 : i64 = select(v100, v99, v97 != i64(0));
    let v107 : i64 = select(i64(0), i64(1), u64(w[1952u + e]) < u64(v101));
    let v108 : i64 = w[64u + e] - v101;
    let v109 : i64 = v108 + w[1952u + e];
    let v110 : i64 = w[1952u + e] - v101;
    let v111 : i64 = select(v110, v109, v107 != i64(0));
    w[3616u + e] = v111;
  }
}
