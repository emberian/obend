// obend-emit-gpu: soac-no-segments, stage 1 of 3: 24 kernels, 12 threads.
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
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_add(acc, w[0u + start + j]);
    }
    w[0u + e] = acc;
  }
  if (t >= 1u && t < 2u) {
    let e : u32 = t - 1u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_add(acc, w[0u + start + j]);
      w[1u + start + j] = acc;
    }
  }
  if (t >= 2u && t < 3u) {
    let e : u32 = t - 2u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[1u + start + j] = acc;
      acc = u64_add(acc, w[0u + start + j]);
    }
  }
  if (t >= 3u && t < 3u) {
    let e : u32 = t - 3u;
  }
  if (t >= 3u && t < 3u) {
    let e : u32 = t - 3u;
  }
  if (t >= 3u && t < 3u) {
    let e : u32 = t - 3u;
  }
  if (t >= 3u && t < 4u) {
    let e : u32 = t - 3u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_mul(acc, w[0u + start + j]);
    }
    w[1u + e] = acc;
  }
  if (t >= 4u && t < 5u) {
    let e : u32 = t - 4u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_mul(acc, w[0u + start + j]);
      w[2u + start + j] = acc;
    }
  }
  if (t >= 5u && t < 6u) {
    let e : u32 = t - 5u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[2u + start + j] = acc;
      acc = u64_mul(acc, w[0u + start + j]);
    }
  }
  if (t >= 6u && t < 6u) {
    let e : u32 = t - 6u;
  }
  if (t >= 6u && t < 6u) {
    let e : u32 = t - 6u;
  }
  if (t >= 6u && t < 6u) {
    let e : u32 = t - 6u;
  }
  if (t >= 6u && t < 7u) {
    let e : u32 = t - 6u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
    }
    w[2u + e] = acc;
  }
  if (t >= 7u && t < 8u) {
    let e : u32 = t - 7u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
      w[3u + start + j] = acc;
    }
  }
  if (t >= 8u && t < 9u) {
    let e : u32 = t - 8u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[3u + start + j] = acc;
      acc = acc & w[0u + start + j];
    }
  }
  if (t >= 9u && t < 9u) {
    let e : u32 = t - 9u;
  }
  if (t >= 9u && t < 9u) {
    let e : u32 = t - 9u;
  }
  if (t >= 9u && t < 9u) {
    let e : u32 = t - 9u;
  }
  if (t >= 9u && t < 10u) {
    let e : u32 = t - 9u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
    }
    w[3u + e] = acc;
  }
  if (t >= 10u && t < 11u) {
    let e : u32 = t - 10u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
      w[4u + start + j] = acc;
    }
  }
  if (t >= 11u && t < 12u) {
    let e : u32 = t - 11u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[4u + start + j] = acc;
      acc = acc | w[0u + start + j];
    }
  }
  if (t >= 12u && t < 12u) {
    let e : u32 = t - 12u;
  }
  if (t >= 12u && t < 12u) {
    let e : u32 = t - 12u;
  }
  if (t >= 12u && t < 12u) {
    let e : u32 = t - 12u;
  }
}
