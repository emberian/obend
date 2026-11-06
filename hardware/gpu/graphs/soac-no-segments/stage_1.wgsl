// obend-emit-gpu: soac-no-segments, stage 1 of 3: 24 kernels, 12 threads.
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
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc + w[0u + start + j];
    }
    w[0u + e] = acc;
  }
  if (t >= 1u && t < 2u) {
    let e : u32 = t - 1u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc + w[0u + start + j];
      w[1u + start + j] = acc;
    }
  }
  if (t >= 2u && t < 3u) {
    let e : u32 = t - 2u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      w[1u + start + j] = acc;
      acc = acc + w[0u + start + j];
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
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[0u + start + j];
    }
    w[1u + e] = acc;
  }
  if (t >= 4u && t < 5u) {
    let e : u32 = t - 4u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[0u + start + j];
      w[2u + start + j] = acc;
    }
  }
  if (t >= 5u && t < 6u) {
    let e : u32 = t - 5u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[2u + start + j] = acc;
      acc = acc * w[0u + start + j];
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
    var acc : i64 = i64(-1);
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
    var acc : i64 = i64(-1);
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
    var acc : i64 = i64(-1);
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
    var acc : i64 = i64(0);
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
    var acc : i64 = i64(0);
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
    var acc : i64 = i64(0);
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
