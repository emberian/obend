// obend-emit-gpu: soac-boundaries, stage 1 of 3: 24 kernels, 96 threads.
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
  let t : u32 = gid.x + gid.y * 128u;
  if (t < 1u) {
    let e : u32 = t - 0u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_add(acc, w[0u + start + j]);
    }
    w[8u + e] = acc;
  }
  if (t >= 1u && t < 2u) {
    let e : u32 = t - 1u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_add(acc, w[0u + start + j]);
      w[9u + start + j] = acc;
    }
  }
  if (t >= 2u && t < 3u) {
    let e : u32 = t - 2u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[17u + start + j] = acc;
      acc = u64_add(acc, w[0u + start + j]);
    }
  }
  if (t >= 3u && t < 10u) {
    let e : u32 = t - 3u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_add(acc, w[0u + start + j]);
    }
    w[25u + e] = acc;
  }
  if (t >= 10u && t < 17u) {
    let e : u32 = t - 10u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_add(acc, w[0u + start + j]);
      w[32u + start + j] = acc;
    }
  }
  if (t >= 17u && t < 24u) {
    let e : u32 = t - 17u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[40u + start + j] = acc;
      acc = u64_add(acc, w[0u + start + j]);
    }
  }
  if (t >= 24u && t < 25u) {
    let e : u32 = t - 24u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_mul(acc, w[0u + start + j]);
    }
    w[48u + e] = acc;
  }
  if (t >= 25u && t < 26u) {
    let e : u32 = t - 25u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_mul(acc, w[0u + start + j]);
      w[49u + start + j] = acc;
    }
  }
  if (t >= 26u && t < 27u) {
    let e : u32 = t - 26u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[57u + start + j] = acc;
      acc = u64_mul(acc, w[0u + start + j]);
    }
  }
  if (t >= 27u && t < 34u) {
    let e : u32 = t - 27u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_mul(acc, w[0u + start + j]);
    }
    w[65u + e] = acc;
  }
  if (t >= 34u && t < 41u) {
    let e : u32 = t - 34u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = u64_mul(acc, w[0u + start + j]);
      w[72u + start + j] = acc;
    }
  }
  if (t >= 41u && t < 48u) {
    let e : u32 = t - 41u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(1u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[80u + start + j] = acc;
      acc = u64_mul(acc, w[0u + start + j]);
    }
  }
  if (t >= 48u && t < 49u) {
    let e : u32 = t - 48u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
    }
    w[88u + e] = acc;
  }
  if (t >= 49u && t < 50u) {
    let e : u32 = t - 49u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
      w[89u + start + j] = acc;
    }
  }
  if (t >= 50u && t < 51u) {
    let e : u32 = t - 50u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[97u + start + j] = acc;
      acc = acc & w[0u + start + j];
    }
  }
  if (t >= 51u && t < 58u) {
    let e : u32 = t - 51u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
    }
    w[105u + e] = acc;
  }
  if (t >= 58u && t < 65u) {
    let e : u32 = t - 58u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
      w[112u + start + j] = acc;
    }
  }
  if (t >= 65u && t < 72u) {
    let e : u32 = t - 65u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(4294967295u, 4294967295u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[120u + start + j] = acc;
      acc = acc & w[0u + start + j];
    }
  }
  if (t >= 72u && t < 73u) {
    let e : u32 = t - 72u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
    }
    w[128u + e] = acc;
  }
  if (t >= 73u && t < 74u) {
    let e : u32 = t - 73u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
      w[129u + start + j] = acc;
    }
  }
  if (t >= 74u && t < 75u) {
    let e : u32 = t - 74u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[137u + start + j] = acc;
      acc = acc | w[0u + start + j];
    }
  }
  if (t >= 75u && t < 82u) {
    let e : u32 = t - 75u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
    }
    w[145u + e] = acc;
  }
  if (t >= 82u && t < 89u) {
    let e : u32 = t - 82u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
      w[152u + start + j] = acc;
    }
  }
  if (t >= 89u && t < 96u) {
    let e : u32 = t - 89u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : vec2<u32> = vec2<u32>(0u, 0u);
    for (var j = 0u; j < n; j = j + 1u) {
      w[160u + start + j] = acc;
      acc = acc | w[0u + start + j];
    }
  }
}
