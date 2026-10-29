#!/usr/bin/env python3
"""Print the module graph for REPORT: one line per module — kind (module|legacy), public imports,
private imports, and counts of exposed defs / public theorems / private theorems."""
import os,re
rows=[]
for r,_,fs in os.walk('Obend'):
    for f in sorted(fs):
        if not f.endswith('.lean'): continue
        p=os.path.join(r,f); s=open(p).read(); L=s.split('\n')
        kind='module' if s.startswith('module') else 'legacy'
        pub=[l.split()[-1] for l in L if l.startswith('public import ') or l.startswith('public meta import ')]
        prv=[l.split()[-1] for l in L if l.startswith('import ')]
        sect='@[expose] public section' in s
        pt=sum(1 for l in L if re.match(r'^\s*(@\[[^\]]*\]\s*)*public (theorem|lemma)\b',l))
        at=sum(1 for l in L if re.match(r'^\s*(@\[[^\]]*\]\s*)*(public\s+)?(theorem|lemma)\b',l))
        ed=sum(1 for l in L if re.match(r'^\s*@\[expose\]',l))
        d=sum(1 for l in L if re.match(r'^\s*(@\[[^\]]*\]\s*)*(public\s+)?(meta\s+)?(def|abbrev|inductive|structure|class|instance)\b',l))
        name=p[:-5].replace('/','.')
        rows.append((name,kind,sect,pub,prv,d,ed,pt,at))
rows.sort()
print("| module | kind | public imports | private imports | decls (exposed) | theorems public/all |")
print("|---|---|---|---|---|---|")
for name,kind,sect,pub,prv,d,ed,pt,at in rows:
    k=kind+(' · exposed section' if sect else '')
    exp='all' if sect else str(ed)
    print(f"| `{name}` | {k} | {', '.join(x.replace('Obend.','') for x in pub) or '—'} | {', '.join(x.replace('Obend.','') for x in prv) or '—'} | {d} ({exp}) | {pt}/{at} |")
