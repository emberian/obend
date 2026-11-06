import datetime, hashlib, json, os, pathlib, re, subprocess, sys
root=pathlib.Path('/home/hbox/obend/kernels')
work=root/'resume-measurements'
gpu=root/'hardware/gpu'
sys.path.insert(0,str(gpu/'cost'))
from grade import grade
runner=gpu/'runner/target/release/obend-gpu-run'
env=dict(os.environ,VK_ICD_FILENAMES='/usr/share/vulkan/icd.d/radeon_icd.x86_64.json')
for n in (1024,65536,1048576):
    folder=work/f'generated/ntt-{n}'
    run=subprocess.run([str(runner),str(folder),'--adapter','radv','--bench','1024'],env=env,text=True,capture_output=True)
    (work/f'gpu-ntt-{n}-sustained.txt').write_text('# measured_utc='+datetime.datetime.now(datetime.timezone.utc).isoformat()+'\n'+run.stdout)
    (work/f'gpu-ntt-{n}-stderr.txt').write_text(run.stderr)
    print(run.stdout,flush=True)
    run.check_returncode()
    dumped=subprocess.run([str(runner),str(folder),'--adapter','radv'],env=dict(env,RADV_DEBUG='shaders,shaderstats',MESA_SHADER_CACHE_DISABLE='true'),text=True,capture_output=True)
    dumped.check_returncode()
    raw=work/f'ntt-{n}-radv.txt'
    raw.write_text(dumped.stderr)
    (work/f'ntt-{n}-dump-run.txt').write_text(dumped.stdout)
    adapter=dumped.stdout.strip().splitlines()[-1].split(', on ',1)[1]
    isa=work/f'ntt-{n}-isa.txt'
    subprocess.run([sys.executable,str(gpu/'isa_extract.py'),str(raw),str(folder/'plan.json'),str(isa),adapter],check=True)
    plan=json.loads((folder/'plan.json').read_text())
    records=[r for r in dumped.stderr.split('shader: MESA_SHADER_COMPUTE')[1:] if 'internal: false' in r and f"workgroup_size: {plan['workgroupSize']}, 1, 1" in r and 'disasm:' in r][-len(plan['stages']):]
    assert len(records)==len(plan['stages'])
    for record in records:
        assert set(re.findall(r'\bs([12]): %\d+:vcc\b',record))=={'2'}, 'wave size mismatch'
    result=grade(plan,isa.read_text(),64)
    for stage,source,record in zip(result['stages'],plan['stages'],records):
        observed=int(re.search(r'^Subgroups per SIMD: (\d+)$',record,re.M).group(1))
        assert observed==stage['mesa_max_waves']
        stage['radv_subgroups_per_simd']=observed
        stage['wave_size_evidence']='ACO VCC allocation register class s2 in matching raw RADV shader record'
        stage['logical_workgroup_read_bytes']=source['logicalWorkgroupReadBytes']
        stage['logical_workgroup_write_bytes']=source['logicalWorkgroupWriteBytes']
    result['logical_workgroup_bytes']=sum(s['logical_workgroup_read_bytes']+s['logical_workgroup_write_bytes'] for s in result['stages'])
    result['source_plan_sha256']=hashlib.sha256((folder/'plan.json').read_bytes()).hexdigest()
    result['raw_radv_sha256']=hashlib.sha256(raw.read_bytes()).hexdigest()
    result['measurement']='resumed lane fresh --bench 1024 and compiler dump; 2026-11-06'
    (work/f'ntt-{n}-grade.json').write_text(json.dumps(result,indent=2)+'\n')
    old=json.loads((gpu/f'cost/ntt-{n}-grade.json').read_text())
    numeric_keys=['dispatches','wire_buffer_bytes','code_bytes','logical_bytes','logical_workgroup_bytes','source_plan_sha256']
    assert all(old[k]==result[k] for k in numeric_keys), 'resource values changed'
    assert (gpu/f'isa/ntt-{n}.txt').read_bytes()==isa.read_bytes(), 'fresh ISA changed'
    print(f'PASS ntt-{n}: committed ISA and resource values reproduced',flush=True)
subprocess.run([sys.executable,str(gpu/'cost/gate.py'),'--runner',str(runner),'--work',str(work/'cost-results')],check=True,env=env)
subprocess.run([sys.executable,str(gpu/'baseline/verify_batch.py'),'--runner',str(runner)],check=True,env=env)
