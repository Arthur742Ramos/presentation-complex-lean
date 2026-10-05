#!/usr/bin/env python3
"""Development-only missing-module build. It is NOT the final whole-source replay."""
from pathlib import Path
import re,subprocess,sys
root=Path(__file__).resolve().parent.parent
seen=set();order=[];targets=set(sys.argv[1:])
def visit(name):
 if name in seen:return
 seen.add(name);p=root/(name.replace('.','/')+'.lean')
 if not p.exists():return
 for line in re.findall(r'^(?:public )?import (.+)',p.read_text(),re.M):
  for dep in line.split():visit(dep)
 order.append(name)
for name in targets:visit(name)
for name in order:
 out=root/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
 if out.exists() and name not in targets:
  print('DEVELOPMENT CACHE '+name,flush=True);continue
 print('BUILD '+name,flush=True)
 subprocess.run(['bash','scripts/lean-file.sh',name.replace('.','/')+'.lean'],cwd=root,check=True)
