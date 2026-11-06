// obend-emit-gpu: glmul-4, stage 1 of 2: 1 kernels, 4 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;
@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;


fn u32_mul_wide(a: u32, b: u32) -> vec2<u32> {
  // Bounded u32 operands: the backend emits native low/high u32 products.
  let product = u64(a) * u64(b);
  return vec2<u32>(u32(product), u32(product >> 32u));
}
fn u64_add(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  let lo = a.x + b.x;
  return vec2<u32>(lo, a.y + b.y + select(0u, 1u, lo < a.x));
}
fn u64_sub(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  return vec2<u32>(a.x - b.x, a.y - b.y - select(0u, 1u, a.x < b.x));
}
fn u64_lt(a: vec2<u32>, b: vec2<u32>) -> bool {
  return a.y < b.y || (a.y == b.y && a.x < b.x);
}
fn u64_mul(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  let p = u32_mul_wide(a.x, b.x);
  return vec2<u32>(p.x, p.y + a.x * b.y + a.y * b.x);
}
fn u64_shr(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  if (b.y != 0u || b.x >= 64u) { return vec2<u32>(0u); }
  if (b.x == 0u) { return a; }
  if (b.x >= 32u) { return vec2<u32>(a.y >> (b.x - 32u), 0u); }
  return vec2<u32>((a.x >> b.x) | (a.y << (32u - b.x)), a.y >> b.x);
}
fn u64_shl(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
  if (b.y != 0u || b.x >= 64u) { return vec2<u32>(0u); }
  if (b.x == 0u) { return a; }
  if (b.x >= 32u) { return vec2<u32>(0u, a.x << (b.x - 32u)); }
  return vec2<u32>(a.x << b.x, (a.y << b.x) | (a.x >> (32u - b.x)));
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x + gid.y * 64u;
  if (t < 4u) {
    let e : u32 = t - 0u;
    let v5 : vec2<u32> = w[0u + e] & w[12u + e];
    let v7 : vec2<u32> = w[4u + e] & w[12u + e];
    let v9 : vec2<u32> = u64_mul(v5, v7);
    let v18 : vec2<u32> = v9 & w[12u + e];
    let v13 : vec2<u32> = u64_shr(v9, w[16u + e]);
    let v8 : vec2<u32> = u64_shr(w[4u + e], w[16u + e]);
    let v10 : vec2<u32> = u64_mul(v5, v8);
    let v14 : vec2<u32> = v10 & w[12u + e];
    let v16 : vec2<u32> = u64_add(v13, v14);
    let v6 : vec2<u32> = u64_shr(w[0u + e], w[16u + e]);
    let v11 : vec2<u32> = u64_mul(v6, v7);
    let v15 : vec2<u32> = v11 & w[12u + e];
    let v17 : vec2<u32> = u64_add(v16, v15);
    let v19 : vec2<u32> = v17 & w[12u + e];
    let v20 : vec2<u32> = u64_shl(v19, w[16u + e]);
    let v21 : vec2<u32> = v18 | v20;
    let v32 : vec2<u32> = vec2<u32>(select(0u, 1u, u64_lt(v21, w[8u + e])), 0u);
    let v33 : vec2<u32> = u64_sub(v21, w[8u + e]);
    let v34 : vec2<u32> = select(v33, v21, any(v32 != vec2<u32>(0u)));
    let v12 : vec2<u32> = u64_mul(v6, v8);
    let v22 : vec2<u32> = u64_shr(v10, w[16u + e]);
    let v25 : vec2<u32> = u64_add(v12, v22);
    let v23 : vec2<u32> = u64_shr(v11, w[16u + e]);
    let v26 : vec2<u32> = u64_add(v25, v23);
    let v24 : vec2<u32> = u64_shr(v17, w[16u + e]);
    let v27 : vec2<u32> = u64_add(v26, v24);
    let v28 : vec2<u32> = v27 & w[12u + e];
    let v30 : vec2<u32> = u64_shl(v28, w[16u + e]);
    let v31 : vec2<u32> = u64_sub(v30, v28);
    let v35 : vec2<u32> = u64_sub(w[8u + e], v31);
    let v36 : vec2<u32> = vec2<u32>(select(0u, 1u, u64_lt(v34, v35)), 0u);
    let v37 : vec2<u32> = u64_add(v34, v31);
    let v38 : vec2<u32> = u64_sub(v34, v35);
    let v39 : vec2<u32> = select(v38, v37, any(v36 != vec2<u32>(0u)));
    let v29 : vec2<u32> = u64_shr(v27, w[16u + e]);
    let v40 : vec2<u32> = vec2<u32>(select(0u, 1u, u64_lt(v39, v29)), 0u);
    let v41 : vec2<u32> = u64_sub(w[8u + e], v29);
    let v42 : vec2<u32> = u64_add(v41, v39);
    let v43 : vec2<u32> = u64_sub(v39, v29);
    let v44 : vec2<u32> = select(v43, v42, any(v40 != vec2<u32>(0u)));
    w[0u + e] = v44;
  }
}
