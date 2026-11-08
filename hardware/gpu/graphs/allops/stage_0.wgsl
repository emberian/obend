// obend-emit-gpu: allops, stage 0 of 1: 3 kernels, 3 threads.
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
  if (t < 1u) {
    let e : u32 = t - 0u;
    let v3 : vec2<u32> = u64_mul(c[0u], w[0u + e]);
    let v4 : vec2<u32> = u64_add(u64_mul(w[1u + e], w[2u + e]), w[0u + e]);
    let v6 : vec2<u32> = u64_sub(v3, v4);
    let v5 : vec2<u32> = u64_add(c[1u], vec2<u32>(0u));
    let v7 : vec2<u32> = u64_mul(v6, v5);
    let v8 : vec2<u32> = u64_add(v7, v3);
    w[3u + e] = v8;
  }
  if (t >= 1u && t < 2u) {
    let e : u32 = t - 1u;
    let v4 : vec2<u32> = u64_add(u64_mul(w[1u + e], w[2u + e]), w[0u + e]);
    let v9 : vec2<u32> = u64_mul(c[2u], v4);
    w[4u + e] = v9;
  }
  if (t >= 2u && t < 3u) {
    let e : u32 = t - 2u;
    let v3 : vec2<u32> = u64_mul(c[3u], w[0u + e]);
    let v4 : vec2<u32> = u64_add(u64_mul(w[1u + e], w[2u + e]), w[0u + e]);
    let v6 : vec2<u32> = u64_sub(v3, v4);
    let v5 : vec2<u32> = u64_add(c[4u], vec2<u32>(0u));
    let v7 : vec2<u32> = u64_mul(v6, v5);
    let v8 : vec2<u32> = u64_add(v7, v3);
    let v9 : vec2<u32> = u64_mul(c[5u], v4);
    let v10 : vec2<u32> = select(v9, v8, any(w[0u + e] != vec2<u32>(0u)));
    w[5u + e] = v10;
  }
}
