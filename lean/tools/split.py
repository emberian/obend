"""Split a Lean proof module at declaration boundaries into piece modules.

usage: python3 tools/split.py FILE PLAN.json [--write | --why | --crit | --dependents NAME,...]
PLAN: {"module": "Obend.Core.Proofs.Adequacy", "pieces": [[startLine, "PieceName", "doc"], ...]}
A piece owns every declaration whose block starts in [startLine, nextStart). Blocks may be assigned
non-contiguously by repeating a piece name. Each piece imports the original imports plus the pieces it
references; a declaration referenced from another piece is made `public`. Optional keys: "defs" (a
piece that takes every non-theorem, so proofs need not wait on each other for a definition), "defsdoc",
"move" ({name or line: piece}), "context" ({piece: [lines after the namespace header]}). The original
file becomes the aggregator, `public import`ing every piece. References are found textually, so check
the result by building it."""
import re, sys, json, collections, os
path, planp = sys.argv[1], sys.argv[2]
write = '--write' in sys.argv
L = open(path).read().split('\n')
plan = json.load(open(planp))
decl = re.compile(r"^(\s*)(?:@\[[^\]]*\]\s*)?((?:(?:public|private|protected|noncomputable|partial|unsafe|nonrec)\s+)*)(theorem|def|lemma|abbrev|inductive|structure|instance|opaque|class)\b\s*([^\s:({\[]*)")
# preamble: up to first decl-ish line
first = None
for i, l in enumerate(L):
    if decl.match(l) and not l.startswith('--'):
        first = i; break
def blockstart(i):
    # extend upward over doc comments, attributes, `set_option .. in`, `open .. in`, comments
    j = i
    while j > 0:
        prev = L[j-1]
        s = prev.strip()
        if s.endswith('-/'):
            k = j-1
            while k >= 0 and not (L[k].lstrip().startswith('/-')): k -= 1
            j = k; continue
        if re.match(r'^(set_option .* in|open .* in|@\[.*\]|attribute \[.*\] .* in|--.*)$', s):
            j -= 1; continue
        break
    return j
starts = []
for i, l in enumerate(L):
    m = decl.match(l)
    if m and i >= first:
        # skip nested (indented) decls inside sections? keep top-level only (indent <= 1)
        if len(m.group(1)) > 1: continue
        starts.append((blockstart(i), i, m.group(4), m.group(3)))
# end of body: before `end <Namespace>` trailing
endline = len(L)
for i in range(len(L)-1, -1, -1):
    if L[i].startswith('end '):
        endline = i; break
pre_end = starts[0][0]
preamble = L[:pre_end]
# split preamble into header (module/doc/imports) and context (namespace/open/set_option)
imp_last = max(i for i, l in enumerate(preamble) if re.match(r'^(public )?import ', l))
header = preamble[:imp_last+1]
context = [l for l in preamble[imp_last+1:]]
imports = [l for l in header if re.match(r'^(public )?import ', l)]
doc = header[1:header.index(imports[0])] if header[0].strip() == 'module' else []
blocks = []
for k, (b, d, name, kind) in enumerate(starts):
    e = starts[k+1][0] if k+1 < len(starts) else endline
    blocks.append(dict(b=b, d=d, e=e, name=name, kind=kind))
for S, *_ in plan['pieces']:
    c0 = S - 1
    for k, bl in enumerate(blocks):
        if k + 1 < len(blocks) and bl['d'] < c0 < bl['e']:
            bl['e'] = c0; blocks[k+1]['b'] = c0

ranges = sorted(plan['pieces'], key=lambda r: r[0])
def piece_of(line1):
    p = None
    for s, n, *_ in ranges:
        if line1 >= s: p = n
    return p
for bl in blocks: bl['piece'] = piece_of(bl['d']+1)
for bl in blocks:
    if plan.get('defs') and bl['kind'] not in ('theorem','lemma'): bl['piece'] = plan['defs']
for line, p in plan.get('move', {}).items():
    for bl in blocks:
        if str(bl['d']+1) == line or bl['name'] == line: bl['piece'] = p
short = {}
dotted = {}
for idx, bl in enumerate(blocks):
    nm = bl['name']
    short.setdefault(nm, []).append(idx)
    if '.' not in nm: pass
    else:
        parts = nm.split('.')
        for k in range(2, len(parts)): short.setdefault('.'.join(parts[-k:]), []).append(idx)
        dotted.setdefault(parts[-1], []).append(idx)
tok = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")
strip_comments = re.compile(r'--[^\n]*')
for idx, bl in enumerate(blocks):
    text = '\n'.join(L[bl['b']:bl['e']])
    text = strip_comments.sub('', text)
    deps = set()
    for t in tok.findall(text):
        parts = t.split('.')
        cands = {t, parts[-1]} | {'.'.join(parts[:k]) for k in range(1, len(parts)+1)} | {'.'.join(parts[-k:]) for k in range(1, len(parts)+1)}
        for c in cands:
            for j in short.get(c, []):
                if j < idx: deps.add(j)
        if len(parts) > 1 and bl['kind'] in ('theorem', 'lemma'):
            for j in dotted.get(parts[-1], []):
                if j < idx: deps.add(j)
    bl['deps'] = deps
pieces = [plan['defs']] if plan.get('defs') else []
for s, n, *rest in ranges + [[0, p] for p in plan.get('move', {}).values()]:
    if n not in pieces: pieces.append(n)
pdeps = collections.defaultdict(set)
needpub = set()
for idx, bl in enumerate(blocks):
    for j in bl['deps']:
        if blocks[j]['piece'] != bl['piece']:
            pdeps[bl['piece']].add(blocks[j]['piece']); needpub.add(j)
# simp/instance/macros: public if any later piece
for idx, bl in enumerate(blocks):
    t = '\n'.join(L[bl['b']:bl['d']+1])
    if '@[simp' in t or bl['kind'] in ('instance', 'class', 'structure', 'inductive', 'def', 'abbrev'):
        needpub.add(idx)
# acyclic check
order = []
state = {}
def visit(p, stack=()):
    if state.get(p) == 2: return
    if state.get(p) == 1: raise SystemExit('cycle: ' + ' -> '.join(stack + (p,)))
    state[p] = 1
    for q in sorted(pdeps[p]): visit(q, stack + (p,))
    state[p] = 2; order.append(p)
for p in pieces: visit(p)
size = {p: sum(bl['e']-bl['b'] for bl in blocks if bl['piece'] == p) for p in pieces}
# transitive reduction of imports
def reach(p, seen=None):
    seen = set() if seen is None else seen
    for q in pdeps[p]:
        if q not in seen: seen.add(q); reach(q, seen)
    return seen
direct = {p: {q for q in pdeps[p] if not any(q in reach(r) for r in pdeps[p] if r != q)} for p in pieces}
crit = {}
for p in order: crit[p] = size[p] + max([crit[q] for q in pdeps[p]] or [0])
for p in pieces:
    print(f"{p:28s} {size[p]:5d} lines  crit {crit[p]:5d}  imports {sorted(direct[p])}")
print('total', sum(size.values()), 'critical path', max(crit.values()))
madepub = [blocks[j]['name'] for j in sorted(needpub) if blocks[j]['kind'] in ('theorem', 'lemma') and 'public' not in L[blocks[j]['d']].split(blocks[j]['kind'])[0]]
print('made public:', len(madepub))
if '--band' in sys.argv:
    B=int(sys.argv[sys.argv.index('--band')+1])
    es={};cp={}
    for idx,bl in enumerate(blocks):
        w=bl['e']-bl['b']; es[idx]=max([cp[j] for j in bl['deps']] or [0]); cp[idx]=es[idx]+w
    band={i:es[i]//B for i in es}
    # union-find within band
    par=list(range(len(blocks)))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for idx,bl in enumerate(blocks):
        for j in bl['deps']:
            if band[j]==band[idx]: par[f(idx)]=f(j)
    comps=collections.defaultdict(list)
    for i in range(len(blocks)): comps[(band[i],f(i))].append(i)
    for k in sorted(comps, key=lambda k:(k[0],min(comps[k]))):
        c=comps[k]; w=sum(blocks[i]['e']-blocks[i]['b'] for i in c)
        print(k[0], w, len(c), blocks[c[0]]['d']+1, blocks[c[-1]]['d']+1, ' '.join(blocks[i]['name'] for i in c[:3]), '...', blocks[c[-1]]['name'])
    sys.exit()
if '--dependents' in sys.argv:
    roots=set(sys.argv[sys.argv.index('--dependents')+1].split(','))
    hit=set(i for i,b in enumerate(blocks) if b['name'] in roots)
    for idx,bl in enumerate(blocks):
        if bl['deps'] & hit: hit.add(idx)
    for i in sorted(hit): print(blocks[i]['d']+1, blocks[i]['e']-blocks[i]['b'], blocks[i]['piece'], blocks[i]['name'])
    sys.exit()
if '--crit' in sys.argv:
    cp={}
    for idx,bl in enumerate(blocks):
        w=bl['e']-bl['b']
        cp[idx]=w+max([cp[j] for j in bl['deps']] or [0])
    m=max(cp,key=cp.get); print('decl critical path',cp[m])
    chain=[]; cur=m
    while True:
        chain.append(cur); ds=blocks[cur]['deps']
        if not ds: break
        cur=max(ds,key=lambda j:cp[j])
    for c in chain: print('   ',blocks[c]['d']+1,blocks[c]['e']-blocks[c]['b'],blocks[c]['name'],blocks[c]['piece'])
if '--why' in sys.argv:
    for idx,bl in enumerate(blocks):
        for j in sorted(bl['deps']):
            if blocks[j]['piece']!=bl['piece']:
                print(f"  {bl['piece']}:{bl['name']} -> {blocks[j]['piece']}:{blocks[j]['name']}")
if not write: sys.exit()
mod = plan['module']
base = os.path.splitext(path)[0]
os.makedirs(base, exist_ok=True)
names = {}
for idx in needpub:
    bl = blocks[idx]; l = L[bl['d']]
    m = decl.match(l)
    mods = m.group(2)
    if 'public' in mods: continue
    if 'private' in mods:
        L[bl['d']] = l.replace('private ', 'public ', 1)
    else:
        L[bl['d']] = l[:m.start(2)] + 'public ' + l[m.start(2):]
nsline = [l for l in context if l.startswith('namespace ')]
ns = nsline[0].split()[1] if nsline else None
docs = {n: (d[0] if d else '') for s, n, *d in ranges}
docs.setdefault(plan.get('defs'), plan.get('defsdoc', ''))
for p in pieces: docs.setdefault(p, '')
for p in pieces:
    out = ['module']
    out.append('/- ' + docs[p] + ' -/') if docs[p] else None
    out += imports
    for q in sorted(direct[p]): out.append(f'public import {mod}.{q}')
    out += [l for l in context]
    out += plan.get('context', {}).get(p, [])
    for bl in blocks:
        if bl['piece'] == p: out += L[bl['b']:bl['e']]
    while out and out[-1].strip() == '': out.pop()
    out.append('')
    out.append(f'end {ns}' if ns else '')
    out.append('')
    open(os.path.join(base, p + '.lean'), 'w').write('\n'.join(out))
agg = ['module'] + doc + [f'public import {mod}.{p}' for p in pieces] + ['']
open(path, 'w').write('\n'.join(agg))
