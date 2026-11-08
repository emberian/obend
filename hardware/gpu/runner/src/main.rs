//! obend-gpu-run: run an `obend-emit-gpu` plan directory on a GPU and compare with the Lean model.
//!
//!     obend-gpu-run DIR [--adapter SUBSTR]       run every vector of DIR/expected.tsv; exit 1 on a disagreement
//!     obend-gpu-run --list-adapters              name, backend and driver of every adapter wgpu sees
//!
//! DIR holds `plan.json` (the flat wire buffer's size, every wire's base and length, the constant and
//! index buffers, the boundary wires, one shader file per stage) and `expected.tsv` (one vector per line:
//! index, the input wires, the expected output wires; wires separated by `;`, elements by `,`, signed
//! decimal). Each stage is one compute dispatch over the wire buffer `w`, the constant buffer `c` and the
//! index buffer `ix`; the dispatches are queued in order.
//! An optional `vectors.json` replaces TSV with raw little-endian 64-bit word files:
//! {"format":"u64le","vectors":[{"index":"case","inputs":["in.bin"],"expected":["out.bin"]}]}.
//! Every boundary wire must have one file of exactly its declared byte length, including empty wires.
//! The adapter is chosen by a case-insensitive substring of its name, driver or driver info (`--adapter radv`); without
//! one, the first non-CPU adapter is taken. Words use two u32 limbs; multiplication widening requires shader-int64.
//! --bench N records a batch of device-timestamped transforms, with reset copies outside each interval.
//! Host batch amortized time includes warmups, reset copies, and final query/output readback, divided by all repetitions.

mod device;
use device::{adapter_line, list_adapters, pick_adapter};
use serde::Deserialize;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(Deserialize)]
struct Stage {
    file: String,
    threads: u32,
}

#[derive(Deserialize)]
struct Plan {
    graph: String,
    words: usize,
    #[serde(rename = "workgroupSize")]
    workgroup_size: u32,
    #[serde(rename = "wireBase")]
    wire_base: Vec<usize>,
    #[serde(rename = "wireLen")]
    wire_len: Vec<usize>,
    consts: Vec<String>,
    tables: Vec<u32>,
    inputs: Vec<usize>,
    outputs: Vec<usize>,
    stages: Vec<Stage>,
}

struct Vector {
    index: String,
    inputs: Vec<Vec<i64>>,
    expected: Vec<Vec<i64>>,
}

fn parse_i64s(field: &str) -> Result<Vec<i64>, String> {
    if field.is_empty() {
        return Ok(vec![]);
    }
    field
        .split(',')
        .map(|s| s.trim().parse::<i64>().map_err(|e| format!("bad integer {s:?}: {e}")))
        .collect()
}

/// Wires separated by `;`, each a comma-separated list of elements (an empty wire is written `-`).
fn parse_wires(field: &str) -> Result<Vec<Vec<i64>>, String> {
    if field.is_empty() {
        return Ok(vec![]);
    }
    field
        .split(';')
        .map(|wire| if wire == "-" { Ok(vec![]) } else { parse_i64s(wire) })
        .collect()
}

fn read_vectors(path: &Path) -> Result<Vec<Vector>, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut out = Vec::new();
    for (n, line) in text.lines().enumerate() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.split('\t').collect();
        if parts.len() != 3 {
            return Err(format!("{}:{}: expected 3 tab-separated fields, got {}", path.display(), n + 1, parts.len()));
        }
        out.push(Vector {
            index: parts[0].to_string(),
            inputs: parse_wires(parts[1])?,
            expected: parse_wires(parts[2])?,
        });
    }
    Ok(out)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BinaryVectors {
    format: String,
    vectors: Vec<BinaryVector>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BinaryVector {
    index: String,
    inputs: Vec<PathBuf>,
    expected: Vec<PathBuf>,
}

fn validate_boundaries(plan: &Plan) -> Result<(), String> {
    if plan.wire_base.len() != plan.wire_len.len() {
        return Err("plan wireBase/wireLen lengths differ".into());
    }
    for &wire in plan.inputs.iter().chain(&plan.outputs) {
        let len = *plan.wire_len.get(wire).ok_or("boundary names an invalid wire")?;
        let base = plan.wire_base[wire];
        if base.checked_add(len).is_none_or(|end| end > plan.words) {
            return Err(format!("boundary wire {wire} exceeds plan word buffer"));
        }
    }
    Ok(())
}

fn read_binary_wires(dir: &Path, files: &[PathBuf], ids: &[usize], plan: &Plan) -> Result<Vec<Vec<i64>>, String> {
    if files.len() != ids.len() {
        return Err(format!("binary boundary has {} files, plan requires {}", files.len(), ids.len()));
    }
    files.iter().zip(ids).map(|(file, &wire)| {
        let path = dir.join(file);
        let want = plan.wire_len[wire].checked_mul(8).ok_or("binary wire byte count overflow")?;
        let size = fs::metadata(&path).map_err(|e| format!("{}: {e}", path.display()))?.len();
        if size != want as u64 {
            return Err(format!("{}: wire {wire} requires {want} bytes, got {size}", path.display()));
        }
        let bytes = fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        if bytes.len() != want {
            return Err(format!("{}: size changed while reading", path.display()));
        }
        // i64 is only the legacy runner's storage type: preserve all u64 bit patterns.
        Ok(bytes.chunks_exact(8).map(|b| i64::from_le_bytes(b.try_into().unwrap())).collect())
    }).collect()
}

fn load_vectors(dir: &Path, plan: &Plan) -> Result<Vec<Vector>, String> {
    validate_boundaries(plan)?;
    let json = dir.join("vectors.json");
    let vectors = if json.exists() {
        let manifest: BinaryVectors = serde_json::from_str(
            &fs::read_to_string(&json).map_err(|e| format!("{}: {e}", json.display()))?
        ).map_err(|e| format!("{}: {e}", json.display()))?;
        if manifest.format != "u64le" { return Err("vectors.json format must be u64le".into()); }
        manifest.vectors.into_iter().map(|v| Ok(Vector {
            index: v.index,
            inputs: read_binary_wires(dir, &v.inputs, &plan.inputs, plan)?,
            expected: read_binary_wires(dir, &v.expected, &plan.outputs, plan)?,
        })).collect::<Result<Vec<_>, String>>()?
    } else {
        read_vectors(&dir.join("expected.tsv"))?
    };
    if vectors.is_empty() { return Err("fixture contains no vectors".into()); }
    for v in &vectors {
        for (kind, wires, ids) in [("input", &v.inputs, &plan.inputs), ("output", &v.expected, &plan.outputs)] {
            if wires.len() != ids.len() {
                return Err(format!("vector {}: {} {kind} wires, plan requires {}", v.index, wires.len(), ids.len()));
            }
            for (data, &wire) in wires.iter().zip(ids) {
                if data.len() != plan.wire_len[wire] {
                    return Err(format!("vector {}: {kind} wire {wire} has {} words, plan requires {}", v.index, data.len(), plan.wire_len[wire]));
                }
            }
        }
    }
    Ok(vectors)
}

const BENCH_WARMUPS: usize = 3;
const MAX_BENCH_SAMPLES: usize = 1024;
const MAX_BATCH_DISPATCHES: usize = 65536;
const MAX_BENCH_RESET_BYTES: u64 = 512 * 1024 * 1024;

fn input_bytes(plan: &Plan, v: &Vector) -> Result<Vec<u8>, String> {
    if v.inputs.len() != plan.inputs.len() {
        return Err(format!("vector {}: {} inputs, plan has {}", v.index, v.inputs.len(), plan.inputs.len()));
    }
    let mut bytes = vec![0u8; plan.words.max(1).checked_mul(8).ok_or("wire byte count overflow")?];
    for (wire, vals) in plan.inputs.iter().zip(&v.inputs) {
        let len = *plan.wire_len.get(*wire).ok_or("invalid input wire")?;
        let base = *plan.wire_base.get(*wire).ok_or("invalid input wire base")?;
        if vals.len() != len || base.checked_add(len).is_none_or(|end| end > plan.words) {
            return Err(format!("vector {}: wire {} has invalid length or bounds", v.index, wire));
        }
        for (chunk, value) in bytes[base * 8..(base + len) * 8].chunks_exact_mut(8).zip(vals) {
            chunk.copy_from_slice(&value.to_le_bytes());
        }
    }
    Ok(bytes)
}

fn decode_outputs(data: &[u8], plan: &Plan) -> Vec<Vec<i64>> {
    plan.outputs.iter().map(|wire| {
        let base = plan.wire_base[*wire];
        (0..plan.wire_len[*wire]).map(|e| {
            i64::from_le_bytes(data[(base + e) * 8..(base + e) * 8 + 8].try_into().unwrap())
        }).collect()
    }).collect()
}

// No per-repetition CPU wait/readback. All command buffers are recorded before
// submission, and every repetition starts from the same device-side reset image.
fn benchmark(
    device: &wgpu::Device, queue: &wgpu::Queue, plan: &Plan, first: &Vector,
    pipelines: &[(wgpu::ComputePipeline, (u32, u32))], bind_group: &wgpu::BindGroup,
    w: &wgpu::Buffer, staging: &wgpu::Buffer, bench: usize, wire_bytes: u64,
) -> Result<(), String> {
    let repetitions = bench + BENCH_WARMUPS;
    let count = (2 * repetitions) as u32;
    if count > wgpu::QUERY_SET_MAX_QUERIES {
        return Err("benchmark exceeds query-set capacity".into());
    }
    let queries = device.create_query_set(&wgpu::QuerySetDescriptor {
        label: Some("batched transform timestamps"), ty: wgpu::QueryType::Timestamp, count,
    });
    let query_bytes = count as u64 * 8;
    let resolve = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("batch timing resolve"), size: query_bytes,
        usage: wgpu::BufferUsages::QUERY_RESOLVE | wgpu::BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let read = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("batch timing readback"), size: query_bytes,
        usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
        mapped_at_creation: false,
    });
    let reset = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("immutable benchmark reset image"), size: wire_bytes,
        usage: wgpu::BufferUsages::COPY_SRC | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    queue.write_buffer(&reset, 0, &input_bytes(plan, first)?);
    queue.submit([]);
    device.poll(wgpu::PollType::wait_indefinitely()).map_err(|e| format!("reset upload: {e}"))?;

    let make_encoder = || device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("benchmark batch"),
    });
    let mut encoder = make_encoder();
    let mut commands = Vec::new();
    let mut passes = 0;
    for repetition in 0..repetitions {
        // GPU copy is ordered before the beginning-of-first-pass timestamp.
        encoder.copy_buffer_to_buffer(&reset, 0, w, 0, wire_bytes);
        for (stage, (pipeline, groups)) in pipelines.iter().enumerate() {
            let first_stage = stage == 0;
            let last_stage = stage + 1 == pipelines.len();
            let timestamp_writes = (first_stage || last_stage).then_some(wgpu::ComputePassTimestampWrites {
                query_set: &queries,
                beginning_of_pass_write_index: first_stage.then_some((2 * repetition) as u32),
                end_of_pass_write_index: last_stage.then_some((2 * repetition + 1) as u32),
            });
            {
                let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                    label: None, timestamp_writes,
                });
                pass.set_pipeline(pipeline);
                pass.set_bind_group(0, bind_group, &[]);
                pass.dispatch_workgroups(groups.0, groups.1, 1);
            }
            passes += 1;
            // Preserve the existing AMDVLK command-buffer dispatch bound, but
            // pre-record and submit every buffer together so the CPU never gaps samples.
            if passes == 128 {
                commands.push(encoder.finish());
                encoder = make_encoder();
                passes = 0;
            }
        }
    }
    encoder.resolve_query_set(&queries, 0..count, &resolve, 0);
    encoder.copy_buffer_to_buffer(&resolve, 0, &read, 0, query_bytes);
    encoder.copy_buffer_to_buffer(w, 0, staging, 0, wire_bytes);
    commands.push(encoder.finish());
    let started = std::time::Instant::now();
    queue.submit(commands);
    let (tx, rx) = std::sync::mpsc::channel();
    let tx_output = tx.clone();
    read.slice(..).map_async(wgpu::MapMode::Read, move |r| { let _ = tx.send(r); });
    staging.slice(..).map_async(wgpu::MapMode::Read, move |r| { let _ = tx_output.send(r); });
    device.poll(wgpu::PollType::wait_indefinitely()).map_err(|e| format!("batch poll: {e}"))?;
    for _ in 0..2 {
        rx.recv().map_err(|e| format!("batch map: {e}"))?.map_err(|e| format!("batch map: {e}"))?;
    }
    let host_amortized_us = started.elapsed().as_secs_f64() * 1e6 / repetitions as f64;
    let got = {
        let data = staging.slice(..).get_mapped_range();
        decode_outputs(&data, plan)
    };
    staging.unmap();
    if got != first.expected {
        read.unmap();
        return Err("benchmark final output disagrees with the first input's exact expected output".into());
    }
    let mut gpu_us = Vec::with_capacity(bench);
    {
        let data = read.slice(..).get_mapped_range();
        for repetition in BENCH_WARMUPS..repetitions {
            let offset = repetition * 16;
            let start = u64::from_le_bytes(data[offset..offset + 8].try_into().unwrap());
            let end = u64::from_le_bytes(data[offset + 8..offset + 16].try_into().unwrap());
            let elapsed = end.wrapping_sub(start);
            if elapsed == 0 {
                return Err(format!("benchmark sample {repetition}: zero timestamp interval"));
            }
            gpu_us.push(elapsed as f64 * queue.get_timestamp_period() as f64 / 1000.0);
        }
    }
    read.unmap();
    gpu_us.sort_by(f64::total_cmp);
    let quantile = |n: usize| gpu_us[(gpu_us.len() - 1) * n / 100];
    println!("BENCH\t{}\t{}\t{}\tgpu_us_median={:.3}\tgpu_us_p10={:.3}\tgpu_us_p90={:.3}\thost_batch_amortized_us={:.3}\twarmups={}\tbatch_repetitions={}\tfinal_output=exact",
        plan.graph, bench, plan.stages.len(), quantile(50), quantile(10), quantile(90),
        host_amortized_us, BENCH_WARMUPS, repetitions);
    Ok(())
}

fn run(dir: &Path, want: Option<&str>, bench: usize) -> Result<(), String> {
    let plan: Plan = serde_json::from_str(
        &fs::read_to_string(dir.join("plan.json")).map_err(|e| format!("plan.json: {e}"))?,
    )
    .map_err(|e| format!("plan.json: {e}"))?;
    let vectors = load_vectors(dir, &plan)?;
    if plan.workgroup_size == 0 { return Err("workgroupSize must be positive".into()); }
    let wire_bytes = plan.words.max(1).checked_mul(8).ok_or("wire byte count overflow")? as u64;
    if bench > 0 {
        if bench > MAX_BENCH_SAMPLES || vectors.is_empty() || plan.stages.is_empty() {
            return Err(format!("benchmark needs 1..={MAX_BENCH_SAMPLES} samples, an input vector and a nonempty stage list"));
        }
        let dispatches = (bench + BENCH_WARMUPS).checked_mul(plan.stages.len()).ok_or("batch dispatch count overflow")?;
        if dispatches > MAX_BATCH_DISPATCHES || wire_bytes > MAX_BENCH_RESET_BYTES {
            return Err(format!("benchmark limit: at most {MAX_BATCH_DISPATCHES} total dispatches and {MAX_BENCH_RESET_BYTES} reset bytes"));
        }
    }
    let consts: Vec<i64> = plan
        .consts
        .iter()
        .map(|s| s.parse::<i64>().map_err(|e| format!("plan.json consts {s:?}: {e}")))
        .collect::<Result<_, _>>()?;

    let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
    let adapter = pick_adapter(&instance, want)?;
    let info_line = adapter_line(&adapter);
    let const_bytes = consts.len().max(1).checked_mul(8).ok_or("constant byte count overflow")? as u64;
    let table_bytes = plan.tables.len().max(1).checked_mul(4).ok_or("table byte count overflow")? as u64;
    let limits = adapter.limits();
    for (name, bytes) in [("w", wire_bytes), ("c", const_bytes), ("ix", table_bytes)] {
        if bytes > limits.max_buffer_size || bytes > u64::from(limits.max_storage_buffer_binding_size) {
            return Err(format!("{info_line}: {name} needs {bytes} bytes; max_buffer_size={}, max_storage_buffer_binding_size={}", limits.max_buffer_size, limits.max_storage_buffer_binding_size));
        }
    }
    let timestamps = bench > 0;
    if timestamps && !adapter.features().contains(wgpu::Features::TIMESTAMP_QUERY) {
        return Err(format!("{info_line}: benchmark requires TIMESTAMP_QUERY"));
    }
    let (device, queue) = pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
        label: Some("obend-gpu-run"),
        required_features: wgpu::Features::SHADER_INT64 | if timestamps { wgpu::Features::TIMESTAMP_QUERY } else { wgpu::Features::empty() },
        required_limits: adapter.limits(),
        ..Default::default()
    }))
    .map_err(|e| format!("request_device: {e}"))?;
    device.on_uncaptured_error(std::sync::Arc::new(|e| {
        eprintln!("[wgpu error] {e}");
    }));

    let w = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("w"),
        size: wire_bytes,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let c = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("c"),
        size: const_bytes,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let ix = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("ix"),
        size: table_bytes,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let staging = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("staging"),
        size: wire_bytes,
        usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let mut const_data = vec![0u8; const_bytes as usize];
    for (i, v) in consts.iter().enumerate() {
        const_data[i * 8..i * 8 + 8].copy_from_slice(&v.to_le_bytes());
    }
    queue.write_buffer(&c, 0, &const_data);
    let mut table_data = vec![0u8; table_bytes as usize];
    for (i, v) in plan.tables.iter().enumerate() {
        table_data[i * 4..i * 4 + 4].copy_from_slice(&v.to_le_bytes());
    }
    queue.write_buffer(&ix, 0, &table_data);

    let storage = |read_only: bool| wgpu::BindingType::Buffer {
        ty: wgpu::BufferBindingType::Storage { read_only },
        has_dynamic_offset: false,
        min_binding_size: None,
    };
    let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("w,c,ix"),
        entries: &[
            wgpu::BindGroupLayoutEntry { binding: 0, visibility: wgpu::ShaderStages::COMPUTE, ty: storage(false), count: None },
            wgpu::BindGroupLayoutEntry { binding: 1, visibility: wgpu::ShaderStages::COMPUTE, ty: storage(true), count: None },
            wgpu::BindGroupLayoutEntry { binding: 2, visibility: wgpu::ShaderStages::COMPUTE, ty: storage(true), count: None },
        ],
    });
    let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("w,c,ix"),
        layout: &bgl,
        entries: &[
            wgpu::BindGroupEntry { binding: 0, resource: w.as_entire_binding() },
            wgpu::BindGroupEntry { binding: 1, resource: c.as_entire_binding() },
            wgpu::BindGroupEntry { binding: 2, resource: ix.as_entire_binding() },
        ],
    });
    let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
        label: Some("obend-gpu"),
        bind_group_layouts: &[&bgl],
        push_constant_ranges: &[],
    });

    let mut pipelines = Vec::new();
    for (k, stage) in plan.stages.iter().enumerate() {
        let src = fs::read_to_string(dir.join(&stage.file)).map_err(|e| format!("{}: {e}", stage.file))?;
        let module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some(&stage.file),
            source: wgpu::ShaderSource::Wgsl(src.into()),
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some(&format!("{} stage {k}", plan.graph)),
            layout: Some(&layout),
            module: &module,
            entry_point: Some("main"),
            compilation_options: Default::default(),
            cache: None,
        });
        let groups = stage.threads.div_ceil(plan.workgroup_size).max(1);
        let groups_x = if groups > 65535 { 32768 } else { groups };
        let groups_y = groups.div_ceil(groups_x);
        pipelines.push((pipeline, (groups_x, groups_y)));
    }

    let mut mismatches = 0usize;
    let mut dispatch_secs = 0f64;
    for v in &vectors {
        let bytes = input_bytes(&plan, v)?;
        queue.write_buffer(&w, 0, &bytes);

        // Dispatches are submitted in chunks: AMDVLK ran out of memory with the 64-point NTT's 1670
        // dispatches in one command buffer, RADV and Metal did not. Submissions execute in order, so the
        // stage order is kept.
        // Timed from the first submission to the device reporting every dispatch done; printed, not gated.
        const CHUNK: usize = 128;
        let started = std::time::Instant::now();
        for chunk in pipelines.chunks(CHUNK) {
            let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor { label: Some("stages") });
            for (pipeline, groups) in chunk {
                let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor { label: None, timestamp_writes: None });
                pass.set_pipeline(pipeline);
                pass.set_bind_group(0, &bind_group, &[]);
                pass.dispatch_workgroups(groups.0, groups.1, 1);
            }
            queue.submit([encoder.finish()]);
        }
        device.poll(wgpu::PollType::wait_indefinitely()).map_err(|e| format!("poll: {e}"))?;
        let elapsed = started.elapsed().as_secs_f64();
        dispatch_secs += elapsed;
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor { label: Some("readback") });
        encoder.copy_buffer_to_buffer(&w, 0, &staging, 0, wire_bytes);
        queue.submit([encoder.finish()]);

        let slice = staging.slice(..);
        let (tx, rx) = std::sync::mpsc::channel();
        slice.map_async(wgpu::MapMode::Read, move |r| {
            let _ = tx.send(r);
        });
        device.poll(wgpu::PollType::wait_indefinitely()).map_err(|e| format!("poll: {e}"))?;
        rx.recv().map_err(|e| format!("map: {e}"))?.map_err(|e| format!("map: {e}"))?;
        let got: Vec<Vec<i64>> = {
            let data = slice.get_mapped_range();
            decode_outputs(&data, &plan)
        };
        staging.unmap();

        if got != v.expected {
            mismatches += 1;
            let first = got.iter().zip(&v.expected).enumerate().find_map(|(wire, (a, b))| {
                a.iter().zip(b).enumerate().find_map(|(element, (x, y))|
                    (x != y).then_some((wire, element, *x, *y)))
            });
            println!("  vector {}: first mismatch {:?} (output wire, element, gpu, expected)", v.index, first);
        }
    }
    println!(
        "{}: {} vectors, {} dispatches, {} disagree, {:.3} ms per vector, on {}",
        plan.graph,
        vectors.len(),
        plan.stages.len(),
        mismatches,
        dispatch_secs * 1e3 / vectors.len().max(1) as f64,
        info_line
    );
    if mismatches > 0 {
        return Err(format!("{} of {} vectors disagree", mismatches, vectors.len()));
    }
    if bench > 0 {
        benchmark(&device, &queue, &plan, &vectors[0], &pipelines, &bind_group, &w, &staging, bench, wire_bytes)?;
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--list-adapters") {
        list_adapters();
        return ExitCode::SUCCESS;
    }
    let mut dir: Option<PathBuf> = None;
    let mut want: Option<String> = None;
    let mut bench = 0usize;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--adapter" => want = it.next().cloned(),
            "--bench" => {
                bench = match it.next().and_then(|s| s.parse().ok()).filter(|n| *n > 0 && *n <= MAX_BENCH_SAMPLES) {
                    Some(n) => n,
                    None => { eprintln!("--bench needs a sample count in 1..={MAX_BENCH_SAMPLES}"); return ExitCode::from(2); }
                };
            }
            other if dir.is_none() => dir = Some(PathBuf::from(other)),
            other => {
                eprintln!("unexpected argument {other:?}");
                return ExitCode::from(2);
            }
        }
    }
    let Some(dir) = dir else {
        eprintln!("usage: obend-gpu-run DIR [--adapter SUBSTR] [--bench SAMPLES] | --list-adapters");
        return ExitCode::from(2);
    };
    match run(&dir, want.as_deref(), bench) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("[FAIL] {e}");
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod binary_fixture_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Fixture(PathBuf);
    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let path = std::env::temp_dir().join(format!("obend-binary-fixture-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn write(&self, name: &str, data: impl AsRef<[u8]>) {
            fs::write(self.0.join(name), data).unwrap();
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) { fs::remove_dir_all(&self.0).unwrap(); }
    }
    fn plan() -> Plan {
        serde_json::from_str(r#"{"graph":"binary-test","words":4,"workgroupSize":64,"wireBase":[0,2,4],"wireLen":[2,2,0],"consts":[],"tables":[],"inputs":[0],"outputs":[1,2],"stages":[]}"#).unwrap()
    }
    fn files(f: &Fixture) {
        f.write("input.bin", [0xff; 16]);
        f.write("output.bin", [0x80; 16]);
        f.write("empty.bin", []);
        f.write("vectors.json", r#"{"format":"u64le","vectors":[{"index":"bits","inputs":["input.bin"],"expected":["output.bin","empty.bin"]}]}"#);
    }
    #[test]
    fn binary_preserves_high_bits_and_empty_output() {
        let f = Fixture::new(); files(&f);
        let v = load_vectors(&f.0, &plan()).unwrap();
        assert_eq!(v[0].inputs[0], vec![-1, -1]);
        assert_eq!(v[0].expected[0], vec![i64::from_le_bytes([0x80; 8]); 2]);
        assert!(v[0].expected[1].is_empty());
        assert_eq!(&input_bytes(&plan(), &v[0]).unwrap()[..16], &[0xff; 16]);
    }
    #[test]
    fn binary_rejects_truncated_extra_or_missing_outputs() {
        let f = Fixture::new(); files(&f);
        f.write("output.bin", [0; 15]);
        assert!(load_vectors(&f.0, &plan()).err().unwrap().contains("requires 16 bytes, got 15"));
        f.write("output.bin", [0; 17]);
        assert!(load_vectors(&f.0, &plan()).err().unwrap().contains("requires 16 bytes, got 17"));
        f.write("vectors.json", r#"{"format":"u64le","vectors":[{"index":"missing","inputs":["input.bin"],"expected":[]}]}"#);
        assert!(load_vectors(&f.0, &plan()).err().unwrap().contains("plan requires 2"));
    }
    #[test]
    fn binary_rejects_wrong_format_empty_fixture_and_bad_bounds() {
        let f = Fixture::new();
        f.write("vectors.json", r#"{"format":"u64be","vectors":[]}"#);
        assert!(load_vectors(&f.0, &plan()).err().unwrap().contains("format must be u64le"));
        f.write("vectors.json", r#"{"format":"u64le","vectors":[]}"#);
        assert!(load_vectors(&f.0, &plan()).err().unwrap().contains("no vectors"));
        let mut p = plan(); p.wire_base[1] = usize::MAX;
        assert!(validate_boundaries(&p).is_err());
    }
    #[test]
    fn tsv_fallback_validates_every_output_shape() {
        let f = Fixture::new();
        f.write("expected.tsv", "0\t-1,-1\t2,3;-\n");
        assert!(load_vectors(&f.0, &plan()).is_ok());
        f.write("expected.tsv", "0\t-1,-1\t2,3\n");
        assert!(load_vectors(&f.0, &plan()).err().unwrap().contains("output wires"));
        f.write("expected.tsv", "0\t-1,-1\t2;-\n");
        assert!(load_vectors(&f.0, &plan()).err().unwrap().contains("output wire 1"));
    }
}
