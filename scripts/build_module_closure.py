#!/usr/bin/env python3
import pathlib,re,subprocess,sys,os
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
    source = m.replace('.', '/') + '.lean'
    if os.name == 'nt':
        output = root/'.lake/build/lib/lean'/m.replace('.', '/')
        output.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['lake', 'env', 'lean', '-j1', '-M6144',
                        '-o', str(output)+'.olean', '-i', str(output)+'.ilean', source],
                       cwd=root, check=True)
    else:
        subprocess.run(['bash','scripts/lean-file.sh',source],cwd=root,check=True)
