// obend-emit-gpu: soac-empty, stage 1 of 3: 24 kernels, 48 threads.
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
  if (t >= 3u && t < 6u) {
    let e : u32 = t - 3u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc + w[0u + start + j];
    }
    w[1u + e] = acc;
  }
  if (t >= 6u && t < 9u) {
    let e : u32 = t - 6u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc + w[0u + start + j];
      w[4u + start + j] = acc;
    }
  }
  if (t >= 9u && t < 12u) {
    let e : u32 = t - 9u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      w[4u + start + j] = acc;
      acc = acc + w[0u + start + j];
    }
  }
  if (t >= 12u && t < 13u) {
    let e : u32 = t - 12u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[0u + start + j];
    }
    w[4u + e] = acc;
  }
  if (t >= 13u && t < 14u) {
    let e : u32 = t - 13u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[0u + start + j];
      w[5u + start + j] = acc;
    }
  }
  if (t >= 14u && t < 15u) {
    let e : u32 = t - 14u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[5u + start + j] = acc;
      acc = acc * w[0u + start + j];
    }
  }
  if (t >= 15u && t < 18u) {
    let e : u32 = t - 15u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[0u + start + j];
    }
    w[5u + e] = acc;
  }
  if (t >= 18u && t < 21u) {
    let e : u32 = t - 18u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc * w[0u + start + j];
      w[8u + start + j] = acc;
    }
  }
  if (t >= 21u && t < 24u) {
    let e : u32 = t - 21u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[8u + start + j] = acc;
      acc = acc * w[0u + start + j];
    }
  }
  if (t >= 24u && t < 25u) {
    let e : u32 = t - 24u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
    }
    w[8u + e] = acc;
  }
  if (t >= 25u && t < 26u) {
    let e : u32 = t - 25u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
      w[9u + start + j] = acc;
    }
  }
  if (t >= 26u && t < 27u) {
    let e : u32 = t - 26u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[9u + start + j] = acc;
      acc = acc & w[0u + start + j];
    }
  }
  if (t >= 27u && t < 30u) {
    let e : u32 = t - 27u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
    }
    w[9u + e] = acc;
  }
  if (t >= 30u && t < 33u) {
    let e : u32 = t - 30u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc & w[0u + start + j];
      w[12u + start + j] = acc;
    }
  }
  if (t >= 33u && t < 36u) {
    let e : u32 = t - 33u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(-1);
    for (var j = 0u; j < n; j = j + 1u) {
      w[12u + start + j] = acc;
      acc = acc & w[0u + start + j];
    }
  }
  if (t >= 36u && t < 37u) {
    let e : u32 = t - 36u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
    }
    w[12u + e] = acc;
  }
  if (t >= 37u && t < 38u) {
    let e : u32 = t - 37u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
      w[13u + start + j] = acc;
    }
  }
  if (t >= 38u && t < 39u) {
    let e : u32 = t - 38u;
    let starts = array<u32, 1>(0u);
    let lengths = array<u32, 1>(0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      w[13u + start + j] = acc;
      acc = acc | w[0u + start + j];
    }
  }
  if (t >= 39u && t < 42u) {
    let e : u32 = t - 39u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
    }
    w[13u + e] = acc;
  }
  if (t >= 42u && t < 45u) {
    let e : u32 = t - 42u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      acc = acc | w[0u + start + j];
      w[16u + start + j] = acc;
    }
  }
  if (t >= 45u && t < 48u) {
    let e : u32 = t - 45u;
    let starts = array<u32, 3>(0u, 0u, 0u);
    let lengths = array<u32, 3>(0u, 0u, 0u);
    let start = starts[e];
    let n = lengths[e];
    var acc : i64 = i64(0);
    for (var j = 0u; j < n; j = j + 1u) {
      w[16u + start + j] = acc;
      acc = acc | w[0u + start + j];
    }
  }
}
