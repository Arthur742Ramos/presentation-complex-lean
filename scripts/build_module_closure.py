#!/usr/bin/env python3
import pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parent.parent
seen=set(); order=[]
def visit(m):
    if m in seen:return
    seen.add(m); f=root/(m.replace('.','/')+'.lean')
    if not f.exists():return
    for line in re.findall(r'^(?:public )?import (.+)',f.read_text(),re.M):
        for dep in line.split():visit(dep)
    order.append(m)
for m in sys.argv[1:]:visit(m)
for m in order:
    print('BUILD '+m,flush=True)
    subprocess.run(['bash','scripts/lean-file.sh',m.replace('.','/')+'.lean'],cwd=root,check=True)
