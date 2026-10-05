#!/usr/bin/env python3
import pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parent.parent
seen=set(); order=[]
def visit(m):
    if m in seen:return
    seen.add(m); f=root/(m.replace('.','/')+'.lean')
    if not f.exists():return
    for dep in re.findall(r'^(?:public )?import ([\w.]+)',f.read_text(),re.M):visit(dep)
    order.append(m)
for m in sys.argv[1:]:visit(m)
for m in order:
    print('BUILD '+m,flush=True)
    subprocess.run(['bash','scripts/lean-file.sh',m.replace('.','/')+'.lean'],cwd=root,check=True)
