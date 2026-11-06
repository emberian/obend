// obend-emit-gpu: ntt-64, stage 2 of 19: 2 kernels, 64 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 32u) {
    let e : u32 = t - 0u;
    let v8 : i64 = w[224u + e] & w[96u + e];
    let v10 : i64 = w[256u + e] & w[96u + e];
    let v12 : i64 = v8 * v10;
    let v21 : i64 = v12 & w[96u + e];
    let v16 : i64 = select(i64(0), i64(u64(v12) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v11 : i64 = select(i64(0), i64(u64(w[256u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v13 : i64 = v8 * v11;
    let v17 : i64 = v13 & w[96u + e];
    let v19 : i64 = v16 + v17;
    let v9 : i64 = select(i64(0), i64(u64(w[224u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v14 : i64 = v9 * v10;
    let v18 : i64 = v14 & w[96u + e];
    let v20 : i64 = v19 + v18;
    let v22 : i64 = v20 & w[96u + e];
    let v23 : i64 = select(i64(0), i64(u64(v22) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v24 : i64 = v21 | v23;
    let v35 : i64 = select(i64(0), i64(1), u64(v24) < u64(w[64u + e]));
    let v36 : i64 = v24 - w[64u + e];
    let v37 : i64 = select(v36, v24, v35 != i64(0));
    let v15 : i64 = v9 * v11;
    let v25 : i64 = select(i64(0), i64(u64(v13) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v28 : i64 = v15 + v25;
    let v26 : i64 = select(i64(0), i64(u64(v14) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v29 : i64 = v28 + v26;
    let v27 : i64 = select(i64(0), i64(u64(v20) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v30 : i64 = v29 + v27;
    let v31 : i64 = v30 & w[96u + e];
    let v33 : i64 = select(i64(0), i64(u64(v31) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v34 : i64 = v33 - v31;
    let v38 : i64 = w[64u + e] - v34;
    let v39 : i64 = select(i64(0), i64(1), u64(v37) < u64(v38));
    let v40 : i64 = v37 + v34;
    let v41 : i64 = v37 - v38;
    let v42 : i64 = select(v41, v40, v39 != i64(0));
    let v32 : i64 = select(i64(0), i64(u64(v30) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v43 : i64 = select(i64(0), i64(1), u64(v42) < u64(v32));
    let v44 : i64 = w[64u + e] - v32;
    let v45 : i64 = v44 + v42;
    let v46 : i64 = v42 - v32;
    let v47 : i64 = select(v46, v45, v43 != i64(0));
    let v48 : i64 = w[64u + e] - v47;
    let v49 : i64 = select(i64(0), i64(1), u64(w[192u + e]) < u64(v48));
    let v50 : i64 = w[192u + e] + v47;
    let v51 : i64 = w[192u + e] - v48;
    let v52 : i64 = select(v51, v50, v49 != i64(0));
    w[1696u + e] = v52;
  }
  if (t >= 32u && t < 64u) {
    let e : u32 = t - 32u;
    let v8 : i64 = w[224u + e] & w[96u + e];
    let v10 : i64 = w[256u + e] & w[96u + e];
    let v12 : i64 = v8 * v10;
    let v21 : i64 = v12 & w[96u + e];
    let v16 : i64 = select(i64(0), i64(u64(v12) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v11 : i64 = select(i64(0), i64(u64(w[256u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v13 : i64 = v8 * v11;
    let v17 : i64 = v13 & w[96u + e];
    let v19 : i64 = v16 + v17;
    let v9 : i64 = select(i64(0), i64(u64(w[224u + e]) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v14 : i64 = v9 * v10;
    let v18 : i64 = v14 & w[96u + e];
    let v20 : i64 = v19 + v18;
    let v22 : i64 = v20 & w[96u + e];
    let v23 : i64 = select(i64(0), i64(u64(v22) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v24 : i64 = v21 | v23;
    let v35 : i64 = select(i64(0), i64(1), u64(v24) < u64(w[64u + e]));
    let v36 : i64 = v24 - w[64u + e];
    let v37 : i64 = select(v36, v24, v35 != i64(0));
    let v15 : i64 = v9 * v11;
    let v25 : i64 = select(i64(0), i64(u64(v13) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v28 : i64 = v15 + v25;
    let v26 : i64 = select(i64(0), i64(u64(v14) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v29 : i64 = v28 + v26;
    let v27 : i64 = select(i64(0), i64(u64(v20) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v30 : i64 = v29 + v27;
    let v31 : i64 = v30 & w[96u + e];
    let v33 : i64 = select(i64(0), i64(u64(v31) << (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v34 : i64 = v33 - v31;
    let v38 : i64 = w[64u + e] - v34;
    let v39 : i64 = select(i64(0), i64(1), u64(v37) < u64(v38));
    let v40 : i64 = v37 + v34;
    let v41 : i64 = v37 - v38;
    let v42 : i64 = select(v41, v40, v39 != i64(0));
    let v32 : i64 = select(i64(0), i64(u64(v30) >> (u32(w[128u + e]) & 63u)), u64(w[128u + e]) < u64(64));
    let v43 : i64 = select(i64(0), i64(1), u64(v42) < u64(v32));
    let v44 : i64 = w[64u + e] - v32;
    let v45 : i64 = v44 + v42;
    let v46 : i64 = v42 - v32;
    let v47 : i64 = select(v46, v45, v43 != i64(0));
    let v53 : i64 = select(i64(0), i64(1), u64(w[192u + e]) < u64(v47));
    let v54 : i64 = w[64u + e] - v47;
    let v55 : i64 = v54 + w[192u + e];
    let v56 : i64 = w[192u + e] - v47;
    let v57 : i64 = select(v56, v55, v53 != i64(0));
    w[1856u + e] = v57;
  }
}
