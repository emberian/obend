// obend-emit-gpu: tree512, stage 5 of 9: 8 kernels, 8 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[1008u + e] = w[992u + e] + w[993u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[1009u + e] = w[994u + e] + w[995u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[1010u + e] = w[996u + e] + w[997u + e]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[1011u + e] = w[998u + e] + w[999u + e]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[1012u + e] = w[1000u + e] + w[1001u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[1013u + e] = w[1002u + e] + w[1003u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[1014u + e] = w[1004u + e] + w[1005u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[1015u + e] = w[1006u + e] + w[1007u + e]; }
}
