// obend-emit-gpu: glmul-4, stage 1 of 2: 1 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 4u) {
    let e : u32 = t - 0u;
    let v5 : i64 = w[0u + e] & w[12u + e];
    let v7 : i64 = w[4u + e] & w[12u + e];
    let v9 : i64 = v5 * v7;
    let v18 : i64 = v9 & w[12u + e];
    let v13 : i64 = i64(u64(v9) >> u32(w[16u + e]));
    let v8 : i64 = i64(u64(w[4u + e]) >> u32(w[16u + e]));
    let v10 : i64 = v5 * v8;
    let v14 : i64 = v10 & w[12u + e];
    let v16 : i64 = v13 + v14;
    let v6 : i64 = i64(u64(w[0u + e]) >> u32(w[16u + e]));
    let v11 : i64 = v6 * v7;
    let v15 : i64 = v11 & w[12u + e];
    let v17 : i64 = v16 + v15;
    let v19 : i64 = v17 & w[12u + e];
    let v20 : i64 = i64(u64(v19) << u32(w[16u + e]));
    let v21 : i64 = v18 | v20;
    let v32 : i64 = select(i64(0), i64(1), u64(v21) < u64(w[8u + e]));
    let v33 : i64 = v21 - w[8u + e];
    let v34 : i64 = select(v33, v21, v32 != i64(0));
    let v12 : i64 = v6 * v8;
    let v22 : i64 = i64(u64(v10) >> u32(w[16u + e]));
    let v25 : i64 = v12 + v22;
    let v23 : i64 = i64(u64(v11) >> u32(w[16u + e]));
    let v26 : i64 = v25 + v23;
    let v24 : i64 = i64(u64(v17) >> u32(w[16u + e]));
    let v27 : i64 = v26 + v24;
    let v28 : i64 = v27 & w[12u + e];
    let v30 : i64 = i64(u64(v28) << u32(w[16u + e]));
    let v31 : i64 = v30 - v28;
    let v35 : i64 = w[8u + e] - v31;
    let v36 : i64 = select(i64(0), i64(1), u64(v34) < u64(v35));
    let v37 : i64 = v34 + v31;
    let v38 : i64 = v34 - v35;
    let v39 : i64 = select(v38, v37, v36 != i64(0));
    let v29 : i64 = i64(u64(v27) >> u32(w[16u + e]));
    let v40 : i64 = select(i64(0), i64(1), u64(v39) < u64(v29));
    let v41 : i64 = w[8u + e] - v29;
    let v42 : i64 = v41 + v39;
    let v43 : i64 = v39 - v29;
    let v44 : i64 = select(v43, v42, v40 != i64(0));
    w[176u + e] = v44;
  }
}
