#!/usr/bin/env python3
"""Replay every submitted module serially from its source, in dependency order."""
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent.parent
modules=[]
for folder in ['Lean4','ClassicalSVK','FiniteGraphFreeGroup','CellAttachment','PresentationComplex']:
    for source in sorted((root/folder).rglob('*.lean')):
        modules.append('.'.join(source.relative_to(root).with_suffix('').parts))
for name in ['Lean4','ClassicalSVK','FiniteGraphFreeGroup','CellAttachment','PresentationComplex','Challenge','Solution']:
    if (root/(name+'.lean')).exists():modules.append(name)
subprocess.run([sys.executable,str(root/'scripts/build_module_closure.py'),*modules],cwd=root,check=True)
if (root/'reports/AuditSolution.lean').exists():
    subprocess.run(['bash','scripts/lean-file.sh','reports/AuditSolution.lean'],cwd=root,check=True)
print('PASS: every submitted proof module and audit source compiled',flush=True)
