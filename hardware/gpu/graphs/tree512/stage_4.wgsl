// obend-emit-gpu: tree512, stage 4 of 9: 16 kernels, 16 threads.
// Generated from Obend.Hardware.Gpu.lowerArrayToGpu; do not edit (verify_gpu.sh compares bytes).
@group(0) @binding(0) var<storage, read_write> w : array<i64>;
@group(0) @binding(1) var<storage, read> c : array<i64>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let t : u32 = gid.x;
  if (t < 1u) { let e : u32 = t - 0u; w[992u + e] = w[960u + e] + w[961u + e]; }
  if (t >= 1u && t < 2u) { let e : u32 = t - 1u; w[993u + e] = w[962u + e] + w[963u + e]; }
  if (t >= 2u && t < 3u) { let e : u32 = t - 2u; w[994u + e] = w[964u + e] + w[965u + e]; }
  if (t >= 3u && t < 4u) { let e : u32 = t - 3u; w[995u + e] = w[966u + e] + w[967u + e]; }
  if (t >= 4u && t < 5u) { let e : u32 = t - 4u; w[996u + e] = w[968u + e] + w[969u + e]; }
  if (t >= 5u && t < 6u) { let e : u32 = t - 5u; w[997u + e] = w[970u + e] + w[971u + e]; }
  if (t >= 6u && t < 7u) { let e : u32 = t - 6u; w[998u + e] = w[972u + e] + w[973u + e]; }
  if (t >= 7u && t < 8u) { let e : u32 = t - 7u; w[999u + e] = w[974u + e] + w[975u + e]; }
  if (t >= 8u && t < 9u) { let e : u32 = t - 8u; w[1000u + e] = w[976u + e] + w[977u + e]; }
  if (t >= 9u && t < 10u) { let e : u32 = t - 9u; w[1001u + e] = w[978u + e] + w[979u + e]; }
  if (t >= 10u && t < 11u) { let e : u32 = t - 10u; w[1002u + e] = w[980u + e] + w[981u + e]; }
  if (t >= 11u && t < 12u) { let e : u32 = t - 11u; w[1003u + e] = w[982u + e] + w[983u + e]; }
  if (t >= 12u && t < 13u) { let e : u32 = t - 12u; w[1004u + e] = w[984u + e] + w[985u + e]; }
  if (t >= 13u && t < 14u) { let e : u32 = t - 13u; w[1005u + e] = w[986u + e] + w[987u + e]; }
  if (t >= 14u && t < 15u) { let e : u32 = t - 14u; w[1006u + e] = w[988u + e] + w[989u + e]; }
  if (t >= 15u && t < 16u) { let e : u32 = t - 15u; w[1007u + e] = w[990u + e] + w[991u + e]; }
}
