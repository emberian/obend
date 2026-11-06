//! obend-gpu-litmus: run the GPUHarbor litmus suite of `hardware/gpu/litmus/` on a GPU through wgpu.
//!
//!     obend-gpu-litmus SUITE_DIR [--adapter SUBSTR] [--configs N] [--iterations N] [--seed STR]
//!                      [--tests a,b,...] [--out FILE]
//!     obend-gpu-litmus --list-adapters
//!
//! The host side is a port of GPUHarbor's `components/litmus-setup.js` and the parameter space of
//! `randomConfig` in `components/test-page-utils.js` (Levine, Guo, Huang, Ma, Chau, Sorensen,
//! "GPUHarbor: Testing GPU Memory Consistency at Large", ISCA 2023; github.com/reeselevine/webgpu-litmus,
//! Apache-2.0), itself the tuned-stress method of Kirkham, Sorensen, Tureci, Martonosi, "Foundations
//! of Empirical Memory Consistency Testing", OOPSLA 2020. Nothing in the test shapes, the stress
//! kernels or the parameter ranges is ours:
//!
//! * every iteration dispatches `numWorkgroups` workgroups of `workgroupSize` threads; the first
//!   `testingWorkgroups` (after an optional shuffle) run the litmus test, one instance per thread pair
//!   (`id_0`, `id_1`), the second thread of a pair striped into another workgroup for device-scope tests
//!   or permuted within the workgroup for workgroup-scope tests; the remaining workgroups run the memory
//!   stress loop on shared scratch lines;
//! * the per-iteration stress parameters (`do_barrier`, `mem_stress`, `pre_stress`, the stress
//!   patterns, the permutation factors 419 and 1031, the memory stride, the location offset) are drawn
//!   exactly as `setStressParams` draws them, from a configuration drawn as `randomConfig` draws it, with
//!   GPUHarbor's deployed limits (at most 1024 workgroups, workgroup size at most 256);
//! * the PRNG is GPUHarbor's `prng.js` (Park-Miller with `Math.imul` wrap-around), seeded from the
//!   `--seed` string with its `hashCode`, so a seed names a parameter sequence;
//! * outcomes are classified by GPUHarbor's own result kernels (`*-results.wgsl`), one atomic counter per
//!   outcome class; this program only sums the counters.
//!
//! SUITE_DIR/suite.tsv names the tests: `name kernel results scope space aliased`; the number of outputs per
//! instance is the field count of the kernel's `struct ReadResult`, the outcome classes are the fields of the
//! result kernel's `struct TestResults`. The output
//! table (`--out`, default stdout) has one line per test with the summed counters per outcome class,
//! the total number of instances, the largest single-configuration count of the `weak` class and the
//! configuration that produced it.

#[path = "../device.rs"]
mod device;
use device::{adapter_line, adapter_tag, list_adapters, pick_adapter};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// GPUHarbor's `prng.js`: `seed = Math.imul(seed, 16807) % 2147483646`, kept positive.
struct Prng(i32);

impl Prng {
    fn from_seed(seed: &str) -> Prng {
        // hashCode(s): h = (h << 5) - h + c, 32-bit wrap
        let mut h: i32 = 0;
        for c in seed.encode_utf16() {
            h = (h << 5).wrapping_sub(h).wrapping_add(c as i32);
        }
        if h <= 0 {
            h = h.wrapping_add(2147483646);
        }
        Prng(h)
    }
    fn next(&mut self) -> u32 {
        let mut s = self.0.wrapping_mul(16807) % 2147483646;
        if s < 0 {
            s += 2147483646;
        }
        self.0 = s;
        s as u32
    }
    /// `randomGenerator(min, max)`: `generator() % (max - min + 1) + min`.
    fn range(&mut self, min: u32, max: u32) -> u32 {
        self.next() % (max - min + 1) + min
    }
    /// `roundedPercentage`: a multiple of 5 in 0..=100 (smoothed parameters).
    fn pct(&mut self) -> u32 {
        self.range(0, 100) / 5 * 5
    }
}

/// `randomConfig`'s output, with the fixed defaults it inherits.
#[derive(Clone, Debug)]
struct Config {
    testing_workgroups: u32,
    max_workgroups: u32,
    workgroup_size: u32,
    shuffle_pct: u32,
    barrier_pct: u32,
    mem_stress_pct: u32,
    pre_stress_pct: u32,
    scratch_memory_size: u32,
    mem_stride: u32,
    stress_line_size: u32,
    stress_target_lines: u32,
    mem_stress_iterations: u32,
    pre_stress_iterations: u32,
    stress_strategy_balance_pct: u32,
    mem_stress_store_first_pct: u32,
    mem_stress_store_second_pct: u32,
    pre_stress_store_first_pct: u32,
    pre_stress_store_second_pct: u32,
    permute_first: u32,
    permute_second: u32,
    num_mem_locations: u32,
    num_outputs: u32,
    aliased_memory: bool,
}

const WORKGROUP_LIMITER: u32 = 1024; // NEXT_PUBLIC_TUNING_MAX_WG
const WORKGROUP_SIZE_LIMITER: u32 = 256; // NEXT_PUBLIC_TUNING_MAX_WG_SIZE

fn random_config(g: &mut Prng, num_outputs: u32, aliased: bool) -> Config {
    let testing_workgroups = g.range(2, WORKGROUP_LIMITER);
    let workgroup_size = g.range(1, WORKGROUP_SIZE_LIMITER);
    let max_workgroups = g.range(testing_workgroups, WORKGROUP_LIMITER);
    let stress_line_size = 1u32 << g.range(2, 10);
    let stress_target_lines = g.range(1, 16);
    let mem_stride = g.range(1, 7);
    Config {
        testing_workgroups,
        max_workgroups,
        workgroup_size,
        shuffle_pct: g.pct(),
        barrier_pct: g.pct(),
        mem_stress_pct: g.pct(),
        pre_stress_pct: g.pct(),
        scratch_memory_size: 32 * stress_line_size * stress_target_lines,
        mem_stride,
        stress_line_size,
        stress_target_lines,
        mem_stress_iterations: g.range(0, 1024),
        pre_stress_iterations: g.range(0, 128),
        stress_strategy_balance_pct: g.pct(),
        mem_stress_store_first_pct: g.pct(),
        mem_stress_store_second_pct: g.pct(),
        pre_stress_store_first_pct: g.pct(),
        pre_stress_store_second_pct: g.pct(),
        permute_first: 419,
        // The coherence pages (corr, coww, cowr, corw1, corw2) alias x and y: `aliasedMemory = true` and
        // `permuteSecond = 1`, so y_0 = x_0.
        permute_second: if aliased { 1 } else { 1031 },
        num_mem_locations: 2,
        num_outputs,
        aliased_memory: aliased,
    }
}

impl Config {
    fn show(&self) -> String {
        format!(
            "testingWorkgroups={} maxWorkgroups={} workgroupSize={} shufflePct={} barrierPct={} memStressPct={} preStressPct={} memStride={} stressLineSize={} stressTargetLines={} memStressIterations={} preStressIterations={} stressStrategyBalancePct={} memStressStoreFirstPct={} memStressStoreSecondPct={} preStressStoreFirstPct={} preStressStoreSecondPct={}",
            self.testing_workgroups, self.max_workgroups, self.workgroup_size, self.shuffle_pct, self.barrier_pct,
            self.mem_stress_pct, self.pre_stress_pct, self.mem_stride, self.stress_line_size, self.stress_target_lines,
            self.mem_stress_iterations, self.pre_stress_iterations, self.stress_strategy_balance_pct,
            self.mem_stress_store_first_pct, self.mem_stress_store_second_pct, self.pre_stress_store_first_pct,
            self.pre_stress_store_second_pct
        )
    }
}

struct Test {
    name: String,
    kernel: String,
    results: String,
    scope: String,
    space: String,
    aliased: bool,
}

fn read_suite(dir: &Path) -> Result<Vec<Test>, String> {
    let path = dir.join("suite.tsv");
    let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut out = Vec::new();
    for (n, line) in text.lines().enumerate() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() != 6 {
            return Err(format!("{}:{}: expected 6 tab-separated fields, got {}", path.display(), n + 1, f.len()));
        }
        out.push(Test {
            name: f[0].to_string(),
            kernel: f[1].to_string(),
            results: f[2].to_string(),
            scope: f[3].to_string(),
            space: f[4].to_string(),
            aliased: match f[5] {
                "0" => false,
                "1" => true,
                other => return Err(format!("{}:{}: aliased must be 0 or 1, got {other}", path.display(), n + 1)),
            },
        });
    }
    Ok(out)
}

/// The field names of `struct NAME` in a WGSL source, in declaration order.
fn struct_fields(src: &str, name: &str) -> Result<Vec<String>, String> {
    let start = src.find(&format!("struct {name}")).ok_or(format!("no `struct {name}`"))?;
    let body = &src[start..];
    let open = body.find('{').ok_or("TestResults: no `{`")?;
    let close = body.find('}').ok_or("TestResults: no `}`")?;
    let classes: Vec<String> = body[open + 1..close]
        .split(',')
        .filter_map(|f| f.split(':').next().map(|s| s.trim().to_string()))
        .filter(|s| !s.is_empty())
        .collect();
    if classes.is_empty() {
        return Err(format!("struct {name} has no fields"));
    }
    Ok(classes)
}

/// The outcome classes: the fields of the result kernel's `TestResults` (at most the 4 counters read back).
fn result_classes(src: &str) -> Result<Vec<String>, String> {
    let classes = struct_fields(src, "TestResults")?;
    if classes.len() > 4 {
        return Err(format!("TestResults has {} fields; the result buffer holds 4", classes.len()));
    }
    Ok(classes)
}

/// The outputs per instance: the fields of the kernel's `ReadResult` (r0, r1, ... ), which size `read_results`.
fn read_outputs(src: &str) -> Result<u32, String> {
    Ok(struct_fields(src, "ReadResult")?.len() as u32)
}

struct Gpu {
    device: wgpu::Device,
    queue: wgpu::Queue,
    test_layout: wgpu::BindGroupLayout,
    result_layout: wgpu::BindGroupLayout,
}

fn storage(read_only: bool) -> wgpu::BindingType {
    wgpu::BindingType::Buffer { ty: wgpu::BufferBindingType::Storage { read_only }, has_dynamic_offset: false, min_binding_size: None }
}

fn entry(binding: u32, ty: wgpu::BindingType) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry { binding, visibility: wgpu::ShaderStages::COMPUTE, ty, count: None }
}

fn buffer(device: &wgpu::Device, label: &str, words: u64, usage: wgpu::BufferUsages) -> wgpu::Buffer {
    device.create_buffer(&wgpu::BufferDescriptor { label: Some(label), size: words.max(1) * 4, usage, mapped_at_creation: false })
}

/// The buffers of `setupTest`, sized for one configuration.
struct Buffers {
    test_locations: wgpu::Buffer,
    read_results: wgpu::Buffer,
    test_results: wgpu::Buffer,
    shuffled_workgroups: wgpu::Buffer,
    barrier: wgpu::Buffer,
    scratchpad: wgpu::Buffer,
    scratch_locations: wgpu::Buffer,
    stress_params: wgpu::Buffer,
    staging: wgpu::Buffer,
    test_locations_words: u64,
    read_results_words: u64,
}

fn make_buffers(gpu: &Gpu, c: &Config) -> Buffers {
    let testing_threads = (c.workgroup_size * c.testing_workgroups) as u64;
    let test_locations_words = testing_threads * c.num_mem_locations as u64 * c.mem_stride as u64;
    let read_results_words = c.num_outputs as u64 * testing_threads;
    let rw = wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST;
    let d = &gpu.device;
    Buffers {
        test_locations: buffer(d, "test_locations", test_locations_words, rw),
        read_results: buffer(d, "read_results", read_results_words, rw),
        test_results: buffer(d, "test_results", 4, rw | wgpu::BufferUsages::COPY_SRC),
        shuffled_workgroups: buffer(d, "shuffled_workgroups", c.max_workgroups as u64, rw),
        barrier: buffer(d, "barrier", 1, rw),
        scratchpad: buffer(d, "scratchpad", c.scratch_memory_size as u64, rw),
        scratch_locations: buffer(d, "scratch_locations", c.max_workgroups as u64, rw),
        stress_params: buffer(d, "stress_params", 12, wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST),
        staging: buffer(d, "staging", 4, wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST),
        test_locations_words,
        read_results_words,
    }
}

fn words(v: &[u32]) -> Vec<u8> {
    v.iter().flat_map(|x| x.to_le_bytes()).collect()
}

/// One `runTestIteration`: the parameter draws, the two dispatches, the four counters.
fn run_iteration(gpu: &Gpu, g: &mut Prng, c: &Config, b: &Buffers, test_pipeline: &wgpu::ComputePipeline, test_bg: &wgpu::BindGroup, result_pipeline: &wgpu::ComputePipeline, result_bg: &wgpu::BindGroup) -> Result<[u32; 4], String> {
    let num_workgroups = if c.testing_workgroups == c.max_workgroups {
        c.testing_workgroups
    } else {
        // getRandomInRange(min, max) = min + getRandomInt(max - min); Math.random, not the seeded PRNG,
        // in GPUHarbor; here the seeded one, so a seed names the whole run.
        c.testing_workgroups + g.next() % (c.max_workgroups - c.testing_workgroups)
    };
    let q = &gpu.queue;
    q.write_buffer(&b.test_locations, 0, &vec![0u8; (b.test_locations_words.max(1) * 4) as usize]);
    q.write_buffer(&b.test_results, 0, &[0u8; 16]);
    q.write_buffer(&b.barrier, 0, &[0u8; 4]);
    q.write_buffer(&b.read_results, 0, &vec![0u8; (b.read_results_words.max(1) * 4) as usize]);

    // setShuffledWorkgroups: identity, Fisher-Yates shuffled with probability shufflePct (getRandomInt is
    // Math.random in GPUHarbor; the seeded PRNG here).
    let mut shuffled: Vec<u32> = (0..num_workgroups).collect();
    if g.next() % 100 < c.shuffle_pct {
        for i in (1..num_workgroups as usize).rev() {
            let x = (g.next() % (i as u32 + 1)) as usize;
            shuffled.swap(i, x);
        }
    }
    shuffled.resize(c.max_workgroups as usize, 0);
    q.write_buffer(&b.shuffled_workgroups, 0, &words(&shuffled));

    // setScratchLocations
    let mut scratch_locations = vec![0u32; c.max_workgroups as usize];
    let scratch_num_regions = c.scratch_memory_size / c.stress_line_size;
    let round_robin = g.next() % 100 < c.stress_strategy_balance_pct;
    let mut used: Vec<u32> = Vec::new();
    for i in 0..c.stress_target_lines {
        let mut region = g.next() % scratch_num_regions;
        while used.contains(&region) && used.len() < scratch_num_regions as usize {
            region = g.next() % scratch_num_regions;
        }
        let loc_in_region = g.next() % c.stress_line_size;
        let loc = region * c.stress_line_size + loc_in_region;
        if round_robin {
            let mut j = i;
            while j < num_workgroups {
                scratch_locations[j as usize] = loc;
                j += c.stress_target_lines;
            }
        } else {
            let per = num_workgroups / c.stress_target_lines;
            for j in 0..per {
                let idx = (i * per + j) as usize;
                if idx < scratch_locations.len() {
                    scratch_locations[idx] = loc;
                }
            }
            if i == c.stress_target_lines - 1 && num_workgroups % c.stress_target_lines != 0 {
                for j in 0..num_workgroups % c.stress_target_lines {
                    scratch_locations[(num_workgroups - j - 1) as usize] = loc;
                }
            }
        }
        used.push(region);
    }
    q.write_buffer(&b.scratch_locations, 0, &words(&scratch_locations));

    // setStressParams
    let pattern = |first: bool, second: bool| -> u32 {
        match (first, second) {
            (true, true) => 0,
            (true, false) => 1,
            (false, true) => 2,
            (false, false) => 3,
        }
    };
    let do_barrier = (g.next() % 100 < c.barrier_pct) as u32;
    let mem_stress = (g.next() % 100 < c.mem_stress_pct) as u32;
    let msf = g.next() % 100 < c.mem_stress_store_first_pct;
    let mss = g.next() % 100 < c.mem_stress_store_second_pct;
    let pre_stress = (g.next() % 100 < c.pre_stress_pct) as u32;
    let psf = g.next() % 100 < c.pre_stress_store_first_pct;
    let pss = g.next() % 100 < c.pre_stress_store_second_pct;
    let params: [u32; 12] = [
        do_barrier,
        mem_stress,
        c.mem_stress_iterations,
        pattern(msf, mss),
        pre_stress,
        c.pre_stress_iterations,
        pattern(psf, pss),
        c.permute_first,
        c.permute_second,
        c.testing_workgroups,
        c.mem_stride,
        if c.aliased_memory { 0 } else { c.mem_stride },
    ];
    q.write_buffer(&b.stress_params, 0, &words(&params));

    let mut encoder = gpu.device.create_command_encoder(&wgpu::CommandEncoderDescriptor { label: Some("litmus") });
    {
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor { label: Some("test"), timestamp_writes: None });
        pass.set_pipeline(test_pipeline);
        pass.set_bind_group(0, test_bg, &[]);
        pass.dispatch_workgroups(num_workgroups, 1, 1);
    }
    {
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor { label: Some("results"), timestamp_writes: None });
        pass.set_pipeline(result_pipeline);
        pass.set_bind_group(0, result_bg, &[]);
        pass.dispatch_workgroups(c.testing_workgroups, 1, 1);
    }
    encoder.copy_buffer_to_buffer(&b.test_results, 0, &b.staging, 0, 16);
    q.submit([encoder.finish()]);

    let slice = b.staging.slice(..);
    let (tx, rx) = std::sync::mpsc::channel();
    slice.map_async(wgpu::MapMode::Read, move |r| {
        let _ = tx.send(r);
    });
    gpu.device.poll(wgpu::PollType::wait_indefinitely()).map_err(|e| format!("poll: {e}"))?;
    rx.recv().map_err(|e| format!("map: {e}"))?.map_err(|e| format!("map: {e}"))?;
    let counts = {
        let data = slice.get_mapped_range();
        let mut out = [0u32; 4];
        for (i, v) in out.iter_mut().enumerate() {
            *v = u32::from_le_bytes(data[i * 4..i * 4 + 4].try_into().unwrap());
        }
        out
    };
    b.staging.unmap();
    Ok(counts)
}

struct Opts {
    suite: PathBuf,
    adapter: Option<String>,
    configs: u32,
    iterations: u32,
    seed: String,
    tests: Option<Vec<String>>,
    out: Option<PathBuf>,
}

fn run(o: &Opts) -> Result<(), String> {
    let tests = read_suite(&o.suite)?;
    let tests: Vec<&Test> = match &o.tests {
        None => tests.iter().collect(),
        Some(sel) => {
            for s in sel {
                if !tests.iter().any(|t| &t.name == s) {
                    return Err(format!("no test named {s} in suite.tsv"));
                }
            }
            tests.iter().filter(|t| sel.contains(&t.name)).collect()
        }
    };
    let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
    let adapter = pick_adapter(&instance, o.adapter.as_deref())?;
    let info_line = adapter_line(&adapter);
    let tag = adapter_tag(&adapter);
    let limits = adapter.limits();
    if limits.max_compute_workgroup_size_x < WORKGROUP_SIZE_LIMITER || limits.max_compute_invocations_per_workgroup < WORKGROUP_SIZE_LIMITER {
        return Err(format!("{info_line}: workgroup size limit {} below {WORKGROUP_SIZE_LIMITER}", limits.max_compute_workgroup_size_x));
    }
    let (device, queue) = pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
        label: Some("obend-gpu-litmus"),
        required_features: wgpu::Features::empty(),
        required_limits: limits,
        ..Default::default()
    }))
    .map_err(|e| format!("request_device: {e}"))?;
    device.on_uncaptured_error(std::sync::Arc::new(|e| {
        eprintln!("[wgpu error] {e}");
    }));
    let test_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("litmus"),
        entries: &[
            entry(0, storage(false)),
            entry(1, storage(false)),
            entry(2, storage(true)),
            entry(3, storage(false)),
            entry(4, storage(false)),
            entry(5, storage(false)),
            entry(6, wgpu::BindingType::Buffer { ty: wgpu::BufferBindingType::Uniform, has_dynamic_offset: false, min_binding_size: None }),
        ],
    });
    let result_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("results"),
        entries: &[
            entry(0, storage(false)),
            entry(1, storage(false)),
            entry(2, storage(false)),
            entry(3, wgpu::BindingType::Buffer { ty: wgpu::BufferBindingType::Uniform, has_dynamic_offset: false, min_binding_size: None }),
            entry(4, storage(true)),
        ],
    });
    let gpu = Gpu { device, queue, test_layout, result_layout };
    let test_pl = gpu.device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor { label: Some("litmus"), bind_group_layouts: &[&gpu.test_layout], push_constant_ranges: &[] });
    let result_pl = gpu.device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor { label: Some("results"), bind_group_layouts: &[&gpu.result_layout], push_constant_ranges: &[] });

    let mut lines: Vec<String> = Vec::new();
    lines.push(format!("# obend-gpu-litmus on {info_line}"));
    lines.push(format!("# tag={tag} seed={} configs={} iterations={} (per test: configs x iterations dispatches; instances = classified thread pairs)", o.seed, o.configs, o.iterations));
    lines.push("# GPUHarbor kernels (github.com/reeselevine/webgpu-litmus); parameter space of randomConfig; classes are the result kernel's TestResults fields".to_string());
    lines.push("test\tscope\tspace\titerations\tinstances\toutcomes\tweak\tweak_best\tconfig_best".to_string());

    for t in tests {
        let kernel_src = fs::read_to_string(o.suite.join("wgsl").join(&t.kernel)).map_err(|e| format!("{}: {e}", t.kernel))?;
        let results_src = fs::read_to_string(o.suite.join("wgsl").join(&t.results)).map_err(|e| format!("{}: {e}", t.results))?;
        let classes = result_classes(&results_src).map_err(|e| format!("{}: {e}", t.results))?;
        let outputs = read_outputs(&kernel_src).map_err(|e| format!("{}: {e}", t.kernel))?;
        let kernel = gpu.device.create_shader_module(wgpu::ShaderModuleDescriptor { label: Some(&t.kernel), source: wgpu::ShaderSource::Wgsl(kernel_src.into()) });
        let results = gpu.device.create_shader_module(wgpu::ShaderModuleDescriptor { label: Some(&t.results), source: wgpu::ShaderSource::Wgsl(results_src.into()) });
        // The test's parameter sequence is seeded by the run seed and the test name, so a test can be
        // rerun alone (--tests) with the same configurations.
        let mut g = Prng::from_seed(&format!("{}:{}", o.seed, t.name));
        let mut totals = [0u64; 4];
        let mut weak_best = 0u32;
        let mut config_best = String::from("-");
        let weak_idx = classes.iter().position(|c| c == "weak");
        let started = std::time::Instant::now();
        for _ in 0..o.configs {
            let c = random_config(&mut g, outputs, t.aliased);
            let b = make_buffers(&gpu, &c);
            let constants = [("workgroupXSize", c.workgroup_size as f64)];
            let compile = wgpu::PipelineCompilationOptions { constants: &constants, ..Default::default() };
            let test_pipeline = gpu.device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor { label: Some(&t.name), layout: Some(&test_pl), module: &kernel, entry_point: Some("main"), compilation_options: compile.clone(), cache: None });
            let result_pipeline = gpu.device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor { label: Some(&t.results), layout: Some(&result_pl), module: &results, entry_point: Some("main"), compilation_options: compile, cache: None });
            let test_bg = gpu.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("litmus"),
                layout: &gpu.test_layout,
                entries: &[
                    wgpu::BindGroupEntry { binding: 0, resource: b.test_locations.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 1, resource: b.read_results.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 2, resource: b.shuffled_workgroups.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 3, resource: b.barrier.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 4, resource: b.scratchpad.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 5, resource: b.scratch_locations.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 6, resource: b.stress_params.as_entire_binding() },
                ],
            });
            let result_bg = gpu.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("results"),
                layout: &gpu.result_layout,
                entries: &[
                    wgpu::BindGroupEntry { binding: 0, resource: b.test_locations.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 1, resource: b.read_results.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 2, resource: b.test_results.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 3, resource: b.stress_params.as_entire_binding() },
                    wgpu::BindGroupEntry { binding: 4, resource: b.shuffled_workgroups.as_entire_binding() },
                ],
            });
            gpu.queue.write_buffer(&b.scratchpad, 0, &vec![0u8; (c.scratch_memory_size.max(1) * 4) as usize]);
            let mut config_weak = 0u32;
            for _ in 0..o.iterations {
                let counts = run_iteration(&gpu, &mut g, &c, &b, &test_pipeline, &test_bg, &result_pipeline, &result_bg)?;
                for i in 0..4 {
                    totals[i] += counts[i] as u64;
                }
                if let Some(w) = weak_idx {
                    config_weak += counts[w];
                }
            }
            if config_weak > weak_best || config_best == "-" {
                weak_best = config_weak;
                config_best = c.show();
            }
        }
        let instances: u64 = (0..classes.len()).map(|i| totals[i]).sum();
        let outcomes = classes.iter().enumerate().map(|(i, c)| format!("{c}={}", totals[i])).collect::<Vec<_>>().join(";");
        let weak = weak_idx.map(|w| totals[w].to_string()).unwrap_or_else(|| "-".into());
        eprintln!("  {:<30} {:>12} instances  weak={:<10} {:.1}s", t.name, instances, weak, started.elapsed().as_secs_f64());
        lines.push(format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", t.name, t.scope, t.space, o.configs as u64 * o.iterations as u64, instances, outcomes, weak, weak_best, config_best));
    }
    let text = lines.join("\n") + "\n";
    match &o.out {
        Some(p) => fs::write(p, text).map_err(|e| format!("{}: {e}", p.display()))?,
        None => print!("{text}"),
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--list-adapters") {
        list_adapters();
        return ExitCode::SUCCESS;
    }
    let mut o = Opts { suite: PathBuf::new(), adapter: None, configs: 32, iterations: 64, seed: "obend".into(), tests: None, out: None };
    let mut suite: Option<PathBuf> = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--adapter" => o.adapter = it.next().cloned(),
            "--configs" => o.configs = it.next().and_then(|s| s.parse().ok()).unwrap_or(0),
            "--iterations" => o.iterations = it.next().and_then(|s| s.parse().ok()).unwrap_or(0),
            "--seed" => o.seed = it.next().cloned().unwrap_or_default(),
            "--tests" => o.tests = it.next().map(|s| s.split(',').map(|x| x.to_string()).collect()),
            "--out" => o.out = it.next().map(PathBuf::from),
            other if suite.is_none() => suite = Some(PathBuf::from(other)),
            other => {
                eprintln!("unexpected argument {other:?}");
                return ExitCode::from(2);
            }
        }
    }
    let Some(suite) = suite else {
        eprintln!("usage: obend-gpu-litmus SUITE_DIR [--adapter SUBSTR] [--configs N] [--iterations N] [--seed STR] [--tests a,b] [--out FILE] | --list-adapters");
        return ExitCode::from(2);
    };
    if o.configs == 0 || o.iterations == 0 {
        eprintln!("--configs and --iterations must be positive integers");
        return ExitCode::from(2);
    }
    o.suite = suite;
    match run(&o) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("[FAIL] {e}");
            ExitCode::from(1)
        }
    }
}
