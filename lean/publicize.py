#!/usr/bin/env python3
"""Make public every theorem the last build reported as `Unknown identifier` (an exposed public body
cited a private theorem). Usage: publicize.py build.log"""
import re,sys,os
log=open(sys.argv[1]).read()
names=set(re.findall(r"Unknown identifier `([^`]*)`",log))
if not names: print("nothing to publicize"); sys.exit(0)
files=[os.path.join(r,f) for r,_,fs in os.walk('Obend') for f in fs if f.endswith('.lean')]
for n in sorted(names):
    short=n.split('.')[-1]
    done=False
    for p in files:
        lines=open(p).read().split('\n'); ch=False
        for i,l in enumerate(lines):
            m=re.match(r'^(\s*)((?:@\[[^\]]*\]\s*)*)(theorem|def|abbrev)\s+'+re.escape(short)+r'\b',l)
            if m and 'public' not in l.split(short)[0]:
                lines[i]=m.group(1)+m.group(2)+'public '+l[len(m.group(1))+len(m.group(2)):]; ch=True; done=True
        if ch: open(p,'w').write('\n'.join(lines)); print("public:",short,"in",p)
    if not done: print("NOT FOUND:",n)
