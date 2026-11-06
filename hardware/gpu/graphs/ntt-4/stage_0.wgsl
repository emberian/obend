// ntt-4: generated from ArrayKernel.Program; no transform-specific emission.
@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;
@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;
var<workgroup> shared_words : array<vec2<u32>, 8>;

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
fn main(@builtin(workgroup_id) wid : vec3<u32>, @builtin(local_invocation_id) lid : vec3<u32>) {
  let group = wid.x + wid.y * 1u;
  if (group >= 1u) { return; }
  for (var lane = lid.x; lane < 1u; lane += 64u) {
    let v0 = w[0u + (((group * 1u) + (lane / 1u)) + ((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 0u) * 1u))];
    let v1 = w[0u + (((group * 1u) + (lane / 1u)) + ((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 1u) * 1u))];
    let v2 = w[0u + (((group * 1u) + (lane / 1u)) + ((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 2u) * 1u))];
    let v3 = w[0u + (((group * 1u) + (lane / 1u)) + ((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 3u) * 1u))];
    let v39 = c[0u + ((((lane % 1u) % 1u) + 1u) * 1u)];
    let v4 = vec2<u32>(1u, 4294967295u);
    let v5 = vec2<u32>(4294967295u, 0u);
    let v6 = vec2<u32>(32u, 0u);
    let v7 = vec2<u32>(select(0u, 1u, u64_lt(v0, v4)), 0u);
    let v8 = u64_sub(v0, v4);
    let v9 = select(v8, v0, any(v7 != vec2<u32>(0u)));
    let v10 = vec2<u32>(select(0u, 1u, u64_lt(v1, v4)), 0u);
    let v11 = u64_sub(v1, v4);
    let v12 = select(v11, v1, any(v10 != vec2<u32>(0u)));
    let v13 = vec2<u32>(select(0u, 1u, u64_lt(v2, v4)), 0u);
    let v14 = u64_sub(v2, v4);
    let v15 = select(v14, v2, any(v13 != vec2<u32>(0u)));
    let v16 = vec2<u32>(select(0u, 1u, u64_lt(v3, v4)), 0u);
    let v17 = u64_sub(v3, v4);
    let v18 = select(v17, v3, any(v16 != vec2<u32>(0u)));
    let v19 = u64_sub(v4, v15);
    let v20 = vec2<u32>(select(0u, 1u, u64_lt(v9, v19)), 0u);
    let v21 = u64_add(v9, v15);
    let v22 = u64_sub(v9, v19);
    let v23 = select(v22, v21, any(v20 != vec2<u32>(0u)));
    let v24 = vec2<u32>(select(0u, 1u, u64_lt(v9, v15)), 0u);
    let v25 = u64_sub(v4, v15);
    let v26 = u64_add(v25, v9);
    let v27 = u64_sub(v9, v15);
    let v28 = select(v27, v26, any(v24 != vec2<u32>(0u)));
    let v29 = u64_sub(v4, v18);
    let v30 = vec2<u32>(select(0u, 1u, u64_lt(v12, v29)), 0u);
    let v31 = u64_add(v12, v18);
    let v32 = u64_sub(v12, v29);
    let v33 = select(v32, v31, any(v30 != vec2<u32>(0u)));
    let v34 = vec2<u32>(select(0u, 1u, u64_lt(v12, v18)), 0u);
    let v35 = u64_sub(v4, v18);
    let v36 = u64_add(v35, v12);
    let v37 = u64_sub(v12, v18);
    let v38 = select(v37, v36, any(v34 != vec2<u32>(0u)));
    let v40 = v38 & v5;
    let v41 = u64_shr(v38, v6);
    let v42 = v39 & v5;
    let v43 = u64_shr(v39, v6);
    let v44 = u64_mul(v40, v42);
    let v45 = u64_mul(v40, v43);
    let v46 = u64_mul(v41, v42);
    let v47 = u64_mul(v41, v43);
    let v48 = u64_shr(v44, v6);
    let v49 = v45 & v5;
    let v50 = v46 & v5;
    let v51 = u64_add(v48, v49);
    let v52 = u64_add(v51, v50);
    let v53 = v44 & v5;
    let v54 = v52 & v5;
    let v55 = u64_shl(v54, v6);
    let v56 = v53 | v55;
    let v57 = u64_shr(v45, v6);
    let v58 = u64_shr(v46, v6);
    let v59 = u64_shr(v52, v6);
    let v60 = u64_add(v47, v57);
    let v61 = u64_add(v60, v58);
    let v62 = u64_add(v61, v59);
    let v63 = v62 & v5;
    let v64 = u64_shr(v62, v6);
    let v65 = u64_shl(v63, v6);
    let v66 = u64_sub(v65, v63);
    let v67 = vec2<u32>(select(0u, 1u, u64_lt(v56, v4)), 0u);
    let v68 = u64_sub(v56, v4);
    let v69 = select(v68, v56, any(v67 != vec2<u32>(0u)));
    let v70 = u64_sub(v4, v66);
    let v71 = vec2<u32>(select(0u, 1u, u64_lt(v69, v70)), 0u);
    let v72 = u64_add(v69, v66);
    let v73 = u64_sub(v69, v70);
    let v74 = select(v73, v72, any(v71 != vec2<u32>(0u)));
    let v75 = vec2<u32>(select(0u, 1u, u64_lt(v74, v64)), 0u);
    let v76 = u64_sub(v4, v64);
    let v77 = u64_add(v76, v74);
    let v78 = u64_sub(v74, v64);
    let v79 = select(v78, v77, any(v75 != vec2<u32>(0u)));
    let v80 = u64_sub(v4, v33);
    let v81 = vec2<u32>(select(0u, 1u, u64_lt(v23, v80)), 0u);
    let v82 = u64_add(v23, v33);
    let v83 = u64_sub(v23, v80);
    let v84 = select(v83, v82, any(v81 != vec2<u32>(0u)));
    let v85 = vec2<u32>(select(0u, 1u, u64_lt(v23, v33)), 0u);
    let v86 = u64_sub(v4, v33);
    let v87 = u64_add(v86, v23);
    let v88 = u64_sub(v23, v33);
    let v89 = select(v88, v87, any(v85 != vec2<u32>(0u)));
    let v90 = u64_sub(v4, v79);
    let v91 = vec2<u32>(select(0u, 1u, u64_lt(v28, v90)), 0u);
    let v92 = u64_add(v28, v79);
    let v93 = u64_sub(v28, v90);
    let v94 = select(v93, v92, any(v91 != vec2<u32>(0u)));
    let v95 = vec2<u32>(select(0u, 1u, u64_lt(v28, v79)), 0u);
    let v96 = u64_sub(v4, v79);
    let v97 = u64_add(v96, v28);
    let v98 = u64_sub(v28, v79);
    let v99 = select(v98, v97, any(v95 != vec2<u32>(0u)));
    w[4u + ((((((group * 1u) + (lane / 1u)) / 1u) * 4u) + (((group * 1u) + (lane / 1u)) % 1u)) + (((0u + ((((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 0u) / 1u) % 2u) * 2u)) + ((((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 0u) / 2u) % 2u) * 1u)) * 1u))] = v84;
    w[4u + ((((((group * 1u) + (lane / 1u)) / 1u) * 4u) + (((group * 1u) + (lane / 1u)) % 1u)) + (((0u + ((((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 1u) / 1u) % 2u) * 2u)) + ((((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 1u) / 2u) % 2u) * 1u)) * 1u))] = v89;
    w[4u + ((((((group * 1u) + (lane / 1u)) / 1u) * 4u) + (((group * 1u) + (lane / 1u)) % 1u)) + (((0u + ((((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 2u) / 1u) % 2u) * 2u)) + ((((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 2u) / 2u) % 2u) * 1u)) * 1u))] = v94;
    w[4u + ((((((group * 1u) + (lane / 1u)) / 1u) * 4u) + (((group * 1u) + (lane / 1u)) % 1u)) + (((0u + ((((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 3u) / 1u) % 2u) * 2u)) + ((((((((lane % 1u) / 1u) * 4u) + ((lane % 1u) % 1u)) + 3u) / 2u) % 2u) * 1u)) * 1u))] = v99;
  }
  workgroupBarrier();
  storageBarrier();
}
