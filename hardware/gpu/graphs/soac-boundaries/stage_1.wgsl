// obend-emit-gpu: soac-boundaries, stage 1 of 3: 24 kernels, 96 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) {
    let e : u32 = t - 0u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc + w[8u + start + j];
    }
    w[16u + e] = acc;
  }
  if (t >= 1u && t < 2u) {
    let e : u32 = t - 1u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc + w[8u + start + j];
      w[17u + start + j] = acc;
    }
  }
  if (t >= 2u && t < 3u) {
    let e : u32 = t - 2u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      w[25u + start + j] = acc;
      acc = acc + w[8u + start + j];
    }
  }
  if (t >= 3u && t < 10u) {
    let e : u32 = t - 3u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc + w[8u + start + j];
    }
    w[33u + e] = acc;
  }
  if (t >= 10u && t < 17u) {
    let e : u32 = t - 10u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc + w[8u + start + j];
      w[40u + start + j] = acc;
    }
  }
  if (t >= 17u && t < 24u) {
    let e : u32 = t - 17u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      w[48u + start + j] = acc;
      acc = acc + w[8u + start + j];
    }
  }
  if (t >= 24u && t < 25u) {
    let e : u32 = t - 24u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[8u + start + j];
    }
    w[56u + e] = acc;
  }
  if (t >= 25u && t < 26u) {
    let e : u32 = t - 25u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[8u + start + j];
      w[57u + start + j] = acc;
    }
  }
  if (t >= 26u && t < 27u) {
    let e : u32 = t - 26u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[65u + start + j] = acc;
      acc = acc * w[8u + start + j];
    }
  }
  if (t >= 27u && t < 34u) {
    let e : u32 = t - 27u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[8u + start + j];
    }
    w[73u + e] = acc;
  }
  if (t >= 34u && t < 41u) {
    let e : u32 = t - 34u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[8u + start + j];
      w[80u + start + j] = acc;
    }
  }
  if (t >= 41u && t < 48u) {
    let e : u32 = t - 41u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[88u + start + j] = acc;
      acc = acc * w[8u + start + j];
    }
  }
  if (t >= 48u && t < 49u) {
    let e : u32 = t - 48u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[8u + start + j];
    }
    w[96u + e] = acc;
  }
  if (t >= 49u && t < 50u) {
    let e : u32 = t - 49u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[8u + start + j];
      w[97u + start + j] = acc;
    }
  }
  if (t >= 50u && t < 51u) {
    let e : u32 = t - 50u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[105u + start + j] = acc;
      acc = acc & w[8u + start + j];
    }
  }
  if (t >= 51u && t < 58u) {
    let e : u32 = t - 51u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[8u + start + j];
    }
    w[113u + e] = acc;
  }
  if (t >= 58u && t < 65u) {
    let e : u32 = t - 58u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[8u + start + j];
      w[120u + start + j] = acc;
    }
  }
  if (t >= 65u && t < 72u) {
    let e : u32 = t - 65u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[128u + start + j] = acc;
      acc = acc & w[8u + start + j];
    }
  }
  if (t >= 72u && t < 73u) {
    let e : u32 = t - 72u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[8u + start + j];
    }
    w[136u + e] = acc;
  }
  if (t >= 73u && t < 74u) {
    let e : u32 = t - 73u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[8u + start + j];
      w[137u + start + j] = acc;
    }
  }
  if (t >= 74u && t < 75u) {
    let e : u32 = t - 74u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(8u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      w[145u + start + j] = acc;
      acc = acc | w[8u + start + j];
    }
  }
  if (t >= 75u && t < 82u) {
    let e : u32 = t - 75u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[8u + start + j];
    }
    w[153u + e] = acc;
  }
  if (t >= 82u && t < 89u) {
    let e : u32 = t - 82u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[8u + start + j];
      w[160u + start + j] = acc;
    }
  }
  if (t >= 89u && t < 96u) {
    let e : u32 = t - 89u;
    let starts = array<u32, 7>(0u, 0u, 1u, 4u, 4u, 6u, 8u);
    let lengths = array<u32, 7>(0u, 1u, 3u, 0u, 2u, 2u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      w[168u + start + j] = acc;
      acc = acc | w[8u + start + j];
    }
  }
}
