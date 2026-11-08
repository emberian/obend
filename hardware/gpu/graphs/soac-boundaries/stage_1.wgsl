// soac-boundaries: generated from ArrayKernel.Program; no transform-specific emission.
@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;
@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;
var<workgroup> shared_words : array<vec2<u32>, 1022>;

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
  for (var lane = lid.x; lane < 8u; lane += 64u) {
    let v0 = w[0u + (ix[8u + group] + lane)];
    shared_words[0u + lane] = v0;
  }
  workgroupBarrier();
  storageBarrier();
  for (var lane = lid.x; lane < 4u; lane += 64u) {
    let v0 = shared_words[0u + (2u * lane)];
    let v1 = shared_words[0u + ((2u * lane) + 1u)];
    let v2 = u64_add(v0, v1);
    shared_words[256u + lane] = v2;
  }
  workgroupBarrier();
  storageBarrier();
  for (var lane = lid.x; lane < 2u; lane += 64u) {
    let v0 = shared_words[256u + (2u * lane)];
    let v1 = shared_words[256u + ((2u * lane) + 1u)];
    let v2 = u64_add(v0, v1);
    shared_words[384u + lane] = v2;
  }
  workgroupBarrier();
  storageBarrier();
  for (var lane = lid.x; lane < 1u; lane += 64u) {
    let v0 = shared_words[384u + (2u * lane)];
    let v1 = shared_words[384u + ((2u * lane) + 1u)];
    let v2 = u64_add(v0, v1);
    shared_words[448u + lane] = v2;
  }
  workgroupBarrier();
  storageBarrier();
  for (var lane = lid.x; lane < 1u; lane += 64u) {
    let v0 = shared_words[448u + 0u];
    w[8u + ix[8u + group]] = v0;
  }
  workgroupBarrier();
  storageBarrier();
}
