@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;
@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;
fn addOne(x : vec2<u32>) -> vec2<u32> {
  return vec2<u32>(x.x + 1u, x.y + select(0u, 1u, x.x == 0xffffffffu));
}
@compute @workgroup_size(64)
fn main(@builtin(local_invocation_id) lid : vec3<u32>) {
  w[lid.x] = addOne(w[lid.x]);
}
