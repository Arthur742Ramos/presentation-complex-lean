#!/usr/bin/env python3
"""Perform ordinary Lake builds in source dependency order on constrained hosts.

This does not inject cache traces or substitute artifacts. Every selected
module uses the normal Lake builder. Afterwards the aggregate default-target
build is required as a separate gate.
"""
from pathlib import Path
import re,subprocess,os
root=Path(__file__).resolve().parent.parent
seen=set(); order=[]
def visit(name):
    if name in seen:return
    seen.add(name); p=root/(name.replace('.','/')+'.lean')
    if not p.exists():return
    for line in re.findall(r'^(?:public )?import (.+)',p.read_text(),re.M):
        for dependency in line.split():visit(dependency)
    order.append(name)
for directory in ['Lean4','ClassicalSVK','FiniteGraphFreeGroup','CellAttachment','PresentationComplex','PresentationPackage']:
    for p in sorted((root/directory).rglob('*.lean')):
        visit('.'.join(p.relative_to(root).with_suffix('').parts))
for name in ['Lean4','ClassicalSVK','FiniteGraphFreeGroup','CellAttachment','PresentationComplex','Challenge','Solution']:
    visit(name)
env={**os.environ,'LEAN_NUM_THREADS':'1'}
for i,name in enumerate(order,1):
    print(f'NORMAL LAKE [{i}/{len(order)}] {name}',flush=True)
    subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=root,env=env,check=True)
print('NORMAL LAKE AGGREGATE',flush=True)
subprocess.run(['lake','--no-cache','build'],cwd=root,env=env,check=True)
print('PASS: normal serial and aggregate Lake builds',flush=True)
