//! Adapter selection shared by `obend-gpu-run` and `obend-gpu-litmus`.

pub fn adapter_line(a: &wgpu::Adapter) -> String {
    let i = a.get_info();
    format!("{} [{:?}] driver={} {} type={:?}", i.name, i.backend, i.driver, i.driver_info, i.device_type)
}

/// A short, file-name-safe tag for an adapter: `<vendor-ish name>-<driver>`.
pub fn adapter_tag(a: &wgpu::Adapter) -> String {
    let i = a.get_info();
    let driver = if i.driver.is_empty() { format!("{:?}", i.backend) } else { i.driver.clone() };
    let name = i.name.split(['(', '[']).next().unwrap_or("").trim().to_string();
    let raw = format!("{name}-{driver}");
    raw.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c.to_ascii_lowercase() } else { '-' })
        .collect::<String>()
        .split('-')
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join("-")
}

/// The adapter whose name, driver or driver info contains `want` (case-insensitive); without `want`,
/// the first non-CPU adapter.
pub fn pick_adapter(instance: &wgpu::Instance, want: Option<&str>) -> Result<wgpu::Adapter, String> {
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
        None => adapters.into_iter().find(|a| a.get_info().device_type != wgpu::DeviceType::Cpu),
    };
    chosen.ok_or_else(|| format!("no adapter matches {want:?}; try --list-adapters"))
}

pub fn list_adapters() {
    let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
    for a in instance.enumerate_adapters(wgpu::Backends::all()) {
        let int64 = a.features().contains(wgpu::Features::SHADER_INT64);
        println!("{} int64={} tag={}", adapter_line(&a), int64, adapter_tag(&a));
    }
}
