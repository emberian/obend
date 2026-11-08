@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;
@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;
fn addOne(x : vec2<u32>) -> vec2<u32> {
  return vec2<u32>(x.x + 1u, x.y + select(0u, 1u, x.x == 0xffffffffu));
}
var<workgroup> tile : array<vec2<u32>, 4096>;
@compute @workgroup_size(64)
fn main(@builtin(local_invocation_id) lid : vec3<u32>) {
  let t = lid.x;
  let x = w[t];
  for (var j = 0u; j < 64u; j = j + 1u) { tile[t + j * 64u] = x; }
  workgroupBarrier();
  // Each lane reads a dynamic slot owned by the next lane, preventing
  // compiler scalar replacement while preserving the same output function.
  let next = (t + 1u) % 64u;
  let chosen = w[next].x & 63u;
  w[64u + next] = addOne(tile[next + chosen * 64u]);
}
