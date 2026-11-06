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
//! The adapter is chosen by a case-insensitive substring of its name, driver or driver info (`--adapter radv`); without
//! one, the first non-CPU adapter is taken. The device must offer 64-bit integers in shaders.

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

fn show_wires(wires: &[Vec<i64>]) -> String {
    wires
        .iter()
        .map(|w| if w.is_empty() { "-".to_string() } else { w.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",") })
        .collect::<Vec<_>>()
        .join(";")
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

fn adapter_line(a: &wgpu::Adapter) -> String {
    let i = a.get_info();
    format!("{} [{:?}] driver={} {} type={:?}", i.name, i.backend, i.driver, i.driver_info, i.device_type)
}

fn pick_adapter(instance: &wgpu::Instance, want: Option<&str>) -> Result<wgpu::Adapter, String> {
    let adapters = instance.enumerate_adapters(wgpu::Backends::all());
    if adapters.is_empty() {
        return Err("wgpu sees no adapter".into());
    }
    let chosen = match want {
        Some(w) => {
            let w = w.to_lowercase();
            adapters.into_iter().find(|a| {
                let i = a.get_info();
                i.name.to_lowercase().contains(&w)
                    || i.driver.to_lowercase().contains(&w)
                    || i.driver_info.to_lowercase().contains(&w)
            })
        }
        None => adapters
            .into_iter()
            .find(|a| a.get_info().device_type != wgpu::DeviceType::Cpu),
    };
    chosen.ok_or_else(|| format!("no adapter matches {want:?}; try --list-adapters"))
}

fn run(dir: &Path, want: Option<&str>) -> Result<(), String> {
    let plan: Plan = serde_json::from_str(
        &fs::read_to_string(dir.join("plan.json")).map_err(|e| format!("plan.json: {e}"))?,
    )
    .map_err(|e| format!("plan.json: {e}"))?;
    let vectors = read_vectors(&dir.join("expected.tsv"))?;
    let consts: Vec<i64> = plan
        .consts
        .iter()
        .map(|s| s.parse::<i64>().map_err(|e| format!("plan.json consts {s:?}: {e}")))
        .collect::<Result<_, _>>()?;

    let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
    let adapter = pick_adapter(&instance, want)?;
    let info_line = adapter_line(&adapter);
    if !adapter.features().contains(wgpu::Features::SHADER_INT64) {
        return Err(format!("{info_line}: no SHADER_INT64"));
    }
    let (device, queue) = pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
        label: Some("obend-gpu-run"),
        required_features: wgpu::Features::SHADER_INT64,
        required_limits: adapter.limits(),
        ..Default::default()
    }))
    .map_err(|e| format!("request_device: {e}"))?;
    device.on_uncaptured_error(std::sync::Arc::new(|e| {
        eprintln!("[wgpu error] {e}");
    }));

    let wire_bytes = (plan.words.max(1) * 8) as u64;
    let const_bytes = (consts.len().max(1) * 8) as u64;
    let table_bytes = (plan.tables.len().max(1) * 4) as u64;
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
        pipelines.push((pipeline, groups));
    }

    let mut mismatches = 0usize;
    let mut dispatch_secs = 0f64;
    for v in &vectors {
        if v.inputs.len() != plan.inputs.len() {
            return Err(format!("vector {}: {} inputs, plan has {}", v.index, v.inputs.len(), plan.inputs.len()));
        }
        let mut wires = vec![0i64; plan.words.max(1)];
        for (wire, vals) in plan.inputs.iter().zip(&v.inputs) {
            if vals.len() != plan.wire_len[*wire] {
                return Err(format!("vector {}: wire {} has {} elements, plan says {}", v.index, wire, vals.len(), plan.wire_len[*wire]));
            }
            let b = plan.wire_base[*wire];
            wires[b..b + vals.len()].copy_from_slice(vals);
        }
        let bytes: Vec<u8> = wires.iter().flat_map(|x| x.to_le_bytes()).collect();
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
                pass.dispatch_workgroups(*groups, 1, 1);
            }
            queue.submit([encoder.finish()]);
        }
        device.poll(wgpu::PollType::wait_indefinitely()).map_err(|e| format!("poll: {e}"))?;
        dispatch_secs += started.elapsed().as_secs_f64();
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
            plan.outputs
                .iter()
                .map(|wire| {
                    let b = plan.wire_base[*wire];
                    (0..plan.wire_len[*wire])
                        .map(|e| i64::from_le_bytes(data[(b + e) * 8..(b + e) * 8 + 8].try_into().unwrap()))
                        .collect()
                })
                .collect()
        };
        staging.unmap();

        if got != v.expected {
            mismatches += 1;
            println!("  vector {}: gpu={} expected={}", v.index, show_wires(&got), show_wires(&v.expected));
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
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--list-adapters") {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
        for a in instance.enumerate_adapters(wgpu::Backends::all()) {
            let int64 = a.features().contains(wgpu::Features::SHADER_INT64);
            println!("{} int64={}", adapter_line(&a), int64);
        }
        return ExitCode::SUCCESS;
    }
    let mut dir: Option<PathBuf> = None;
    let mut want: Option<String> = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--adapter" => want = it.next().cloned(),
            other if dir.is_none() => dir = Some(PathBuf::from(other)),
            other => {
                eprintln!("unexpected argument {other:?}");
                return ExitCode::from(2);
            }
        }
    }
    let Some(dir) = dir else {
        eprintln!("usage: obend-gpu-run DIR [--adapter SUBSTR] | --list-adapters");
        return ExitCode::from(2);
    };
    match run(&dir, want.as_deref()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("[FAIL] {e}");
            ExitCode::from(1)
        }
    }
}
