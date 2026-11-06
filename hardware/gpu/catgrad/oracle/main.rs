//! A real catgrad core::Term, serialized by catgrad/open-hypergraphs' own serde derives,
//! and evaluated by catgrad's ndarray interpreter. No obend implementation is used here.
use catgrad::category::core::*;
use catgrad::definition::Def;
use catgrad::interpreter::backend::{Backend, ndarray::NdArrayBackend};
use catgrad::interpreter::{Interpreter, Parameters, TaggedVec, Value, tensor};
use serde_json::json;
use std::time::Instant;

#[allow(dead_code, unexpected_cfgs)]
mod upstream {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/upstream_hidden.rs"));
}
#[allow(dead_code, unexpected_cfgs)]
mod upstream_original {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/upstream_hidden_original.rs"
    ));
}
use catgrad::stdlib::Module;
use std::collections::BTreeMap;

// Specialization of hidden.rs: concrete flattening and parameter loads become input boundaries.
// Architecture comes from the upstream example executed independently below.
fn model() -> (Term, Vec<NdArrayType>) {
    let mut t = Term::empty();
    let shapes = vec![
        vec![2, 784],
        vec![784, 100],
        vec![2, 100],
        vec![100, 10],
        vec![2, 10],
    ];
    let inputs: Vec<_> = shapes.iter().map(|_| t.new_node(Object::Tensor)).collect();
    t.sources = inputs.clone();
    let mut op = |o: Operation, src: Vec<_>, count| {
        let dst: Vec<_> = (0..count).map(|_| t.new_node(Object::Tensor)).collect();
        t.new_edge(Def::Arr(o), (src, dst.clone()));
        dst
    };
    let mut x = inputs[0];
    for (weight, cap) in [(inputs[1], inputs[2]), (inputs[3], inputs[4])] {
        let h = op(Operation::Tensor(TensorOp::MatMul), vec![x, weight], 1)[0];
        let h = op(Operation::Copy, vec![h], 2);
        let cap = op(Operation::Copy, vec![cap], 2);
        let under = op(
            Operation::Tensor(TensorOp::Map(ScalarOp::LT)),
            vec![h[0], cap[0]],
            1,
        )[0];
        x = op(
            Operation::Tensor(TensorOp::Map(ScalarOp::Where)),
            vec![under, h[1], cap[1]],
            1,
        )[0];
    }
    t.targets = vec![x];
    (
        t,
        shapes
            .into_iter()
            .map(|shape| NdArrayType {
                dtype: Dtype::U32,
                shape: Shape(shape),
            })
            .collect(),
    )
}

fn output(result: Vec<Value<NdArrayBackend>>) -> Vec<Vec<u32>> {
    result
        .into_iter()
        .map(|x| match x {
            Value::Tensor(t) => match NdArrayBackend.to_vec(t) {
                TaggedVec::U32(v) => v,
                _ => panic!("dtype"),
            },
            _ => panic!("tensor"),
        })
        .collect()
}

// In this upstream backend, comparisons return U32 (not Bool), and Where tests
// nonzero U32 values. Exercise those compositions and the supported wrapping
// pointwise operators independently of the MLP's MatMul/activation path.
fn scalar_probe(path: &std::path::Path) {
    let mut term = Term::empty();
    let inputs: Vec<_> = (0..3).map(|_| term.new_node(Object::Tensor)).collect();
    term.sources = inputs.clone();
    let mut op = |o: Operation, src: Vec<_>, count| {
        let dst: Vec<_> = (0..count).map(|_| term.new_node(Object::Tensor)).collect();
        term.new_edge(Def::Arr(o), (src, dst.clone()));
        dst
    };
    let a = op(Operation::Copy, vec![inputs[0]], 4);
    let b = op(Operation::Copy, vec![inputs[1]], 5);
    let map = |o| Operation::Tensor(TensorOp::Map(o));
    let sum = op(map(ScalarOp::Add), vec![a[0], b[0]], 1)[0];
    let diff = op(map(ScalarOp::Sub), vec![a[1], b[1]], 1)[0];
    let product = op(map(ScalarOp::Mul), vec![a[2], b[2]], 1)[0];
    let lt = op(map(ScalarOp::LT), vec![a[3], b[3]], 1)[0];
    let predicate_sum = op(map(ScalarOp::Add), vec![lt, b[4]], 1)[0];
    let sum = op(Operation::Copy, vec![sum], 2);
    let diff = op(Operation::Copy, vec![diff], 2);
    let selected = op(map(ScalarOp::Where), vec![inputs[2], sum[1], diff[1]], 1)[0];
    term.targets = vec![sum[0], diff[0], product, predicate_sum, selected];
    let values = vec![
        vec![0, u32::MAX, 0x80000000, u32::MAX],
        vec![1, 2, u32::MAX, u32::MAX],
        vec![0, 1, 2, u32::MAX],
    ];
    let types = vec![
        NdArrayType {
            dtype: Dtype::U32,
            shape: Shape(vec![4])
        };
        3
    ];
    let args = values
        .iter()
        .map(|v| tensor(&NdArrayBackend, Shape(vec![4]), v.clone()).unwrap())
        .collect();
    let interpreter = Interpreter::new(
        NdArrayBackend,
        catgrad::stdlib::stdlib(),
        Parameters::default(),
    );
    let outputs = output(
        interpreter
            .eval(term.clone(), args)
            .expect("scalar boundary interpreter"),
    );
    let doc = json!({"format":"catgrad-core-u32-v1", "name":"catgrad-u32-scalar-boundaries",
        "term":term, "inputTypes":types, "vectors":[{"inputs":values,"outputs":outputs}]});
    std::fs::write(path, serde_json::to_string(&doc).unwrap() + "\n").unwrap();
    println!(
        "catgrad scalar boundary oracle: wrapping Add/Sub/Mul, LT-to-Add and nonzero U32 Where"
    );
}

fn main() {
    let out = std::env::args()
        .nth(1)
        .expect("usage: obend-catgrad-oracle OUTPUT.json");
    let (term, types) = model();
    let model = upstream::SimpleMNISTModel;
    let source = model.term().unwrap();
    let original = upstream_original::SimpleMNISTModel.term().unwrap();
    let paths = [
        catgrad::path::path(vec!["0", "weights"]).unwrap(),
        catgrad::path::path(vec!["1", "weights"]).unwrap(),
    ];
    let mut env = catgrad::stdlib::stdlib();
    env.declarations
        .extend(catgrad::stdlib::to_load_ops(model.path(), paths.iter()));
    let flat_interpreter = Interpreter::new(
        NdArrayBackend,
        catgrad::stdlib::stdlib(),
        Parameters::default(),
    );
    let mut vectors = Vec::new();
    let mut elapsed = 0.0;
    for v in 0..4 {
        let inputs: Vec<Vec<u32>> = types
            .iter()
            .enumerate()
            .map(|(w, t)| {
                (0..t.shape.size())
                    .map(|i| {
                        if w == 2 || w == 4 {
                            600
                        } else if v == 0 {
                            0
                        } else if v == 3 {
                            match w {
                                // Both kinds of overflow must produce 1 before clipping:
                                // even hidden columns sum MAX+2; odd columns multiply MAX*MAX.
                                0 => match i % 784 {
                                    0 => u32::MAX,
                                    1 => 2,
                                    _ => 0,
                                },
                                1 => match (i / 100, i % 2) {
                                    (0, 0) | (1, 0) => 1,
                                    (0, 1) => u32::MAX,
                                    _ => 0,
                                },
                                3 => u32::from(i / 10 == i % 10),
                                _ => unreachable!(),
                            }
                        } else if w == 1 || w == 3 {
                            if i % 17 == 0 { v as u32 } else { 0 }
                        } else {
                            (1 + (i * 13 + w * 7) % v) as u32
                        }
                    })
                    .collect()
            })
            .collect();
        let args: Vec<_> = types
            .iter()
            .zip(&inputs)
            .map(|(t, x)| tensor(&NdArrayBackend, t.shape.clone(), x.clone()).unwrap())
            .collect();
        let mut params = BTreeMap::new();
        params.insert(paths[0].clone(), args[1].clone());
        params.insert(paths[1].clone(), args[3].clone());
        let interpreter = Interpreter::new(NdArrayBackend, env.clone(), Parameters::from(params));
        let source_input =
            tensor(&NdArrayBackend, Shape(vec![2, 28, 28]), inputs[0].clone()).unwrap();
        let start = Instant::now();
        let result = interpreter
            .run(source.term.clone(), vec![source_input])
            .expect("upstream hidden.rs interpreter");
        elapsed += start.elapsed().as_secs_f64();
        let outputs = output(result);
        // Independently check the shape/parameter specialization before serializing it.
        assert_eq!(
            output(flat_interpreter.eval(term.clone(), args).unwrap()),
            outputs
        );
        vectors.push(json!({"inputs":inputs, "outputs":outputs}));
    }
    let doc = json!({"format":"catgrad-core-u32-v1", "name":"catgrad-hidden-u32-2x784x100x10", "term":term,
        "upstreamExample":"catgrad/examples/hidden.rs::SimpleMNISTModel", "sourceTerm":source,
        "originalFloatTerm":original,
        "adaptation":"F32 to U32; both Sigmoid calls replaced by min(x,600); input reshape and parameter loads specialized to boundaries; integer test parameters replace float demonstration parameters",
        "inputTypes":types, "vectors":vectors});
    std::fs::write(&out, serde_json::to_string(&doc).unwrap() + "\n").unwrap();
    println!(
        "catgrad upstream hidden.rs adapted U32 ndarray interpreter: 4 vectors, {:.6} ms per forward pass (source clone, lang-to-core lowering, shape evaluation, loads, term scheduling and evaluation; input tensor construction excluded)",
        elapsed * 1000.0 / 4.0
    );
    scalar_probe(&std::path::Path::new(&out).with_file_name("scalar-ops.json"));
}
