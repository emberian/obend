#!/usr/bin/env python3
"""Pass 1 of the module split (2026-10-30). Adds `module` headers, makes imports public,
wraps DEFINITIONAL modules in `@[expose] public section`, and in PROOF modules marks public
exactly the declarations whose short name another module mentions (plus instances and
attribute-carrying theorems). Run from lean/. Idempotent: skips files that start with `module`."""
import os,re,sys
DEF_MODULES={'Obend/AxiomPin.lean','Obend/AssertAxioms.lean','Obend/AssertCompiled.lean',
 'Obend/Digest/HashBytes.lean','Obend/Digest/Cshake256/Spec.lean','Obend/Digest/Cshake256/Fast.lean',
 'Obend/Digest/Cshake256/Seam.lean','Obend/Digest/Cshake256.lean',
 'Obend/Core/Term.lean','Obend/Core/Ty.lean','Obend/Core/Check.lean','Obend/Core/Machine.lean',
 'Obend/Core/MachineFast.lean','Obend/Core/Invariant.lean','Obend/Core/Data.lean','Obend/Core/Capacity.lean',
 'Obend/Core/Collect.lean','Obend/Core/Checkpoint.lean','Obend/Core/Extensions.lean',
 'Obend/Core/MachineTyping.lean','Obend/Core/Interaction.lean','Obend/Core/Digest.lean'}
DECL=re.compile(r'^(?P<attrs>(?:@\[[^\]]*\]\s*)*)(?P<mods>(?:(?:noncomputable|protected|unsafe|partial)\s+)*)(?P<kind>theorem|lemma|def|abbrev|inductive|structure|class|instance|opaque|axiom)\s+(?P<name>[^\s:(\[{]+)')
files=sorted(os.path.join(r,f) for r,_,fs in os.walk('Obend') for f in fs if f.endswith('.lean'))
src={p:open(p).read() for p in files}
# short names declared per file
decls={}
for p,s in src.items():
    names=[]
    for line in s.splitlines():
        m=DECL.match(line)
        if m and not line.startswith('private'):
            names.append((m.group('name').split('.')[-1], m.group('kind')))
    decls[p]=names
# token sets of other files
tokens={p:set(re.findall(r'[A-Za-z_][A-Za-z0-9_\'!?]*',s)) for p,s in src.items()}
dry='--dry' in sys.argv
report=[]
for p,s in src.items():
    if s.startswith('module'): continue
    lines=s.split('\n')
    # header: find import block
    imps=[i for i,l in enumerate(lines) if l.startswith('import ')]
    for i in imps: lines[i]='public '+lines[i]
    last_imp=max(imps) if imps else -1
    # for files with no imports, insert after leading doc comment block
    if p in DEF_MODULES:
        # insert `module` at top and wrap body after imports
        body_start=last_imp+1
        if last_imp==-1:
            # skip leading block comment
            j=0
            if lines and lines[0].startswith('/-'):
                while not lines[j].rstrip().endswith('-/'): j+=1
                j+=1
            body_start=j
        lines.insert(body_start,'@[expose] public section')
        lines.append('end')
        lines.insert(0,'module')
        report.append((p,'DEF','all public+exposed'))
    else:
        others=set()
        for q,t in tokens.items():
            if q!=p: others|=t
        made=0; total=0
        for i,l in enumerate(lines):
            m=DECL.match(l)
            if not m or l.startswith('private'): continue
            total+=1
            short=m.group('name').split('.')[-1]
            attrs=m.group('attrs')
            need = (short in others) or m.group('kind')=='instance' or ('csimp' in attrs) or ('simp' in attrs)
            if need:
                lines[i]=attrs+'public '+l[len(attrs):]
                made+=1
        lines.insert(0,'module')
        report.append((p,'PROOF',f'{made}/{total} public'))
    if not dry: open(p,'w').write('\n'.join(lines))
for r in report: print(*r)
