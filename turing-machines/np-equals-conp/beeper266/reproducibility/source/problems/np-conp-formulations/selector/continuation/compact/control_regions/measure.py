"""Paid complete architecture measurements with original fixed-kernel backend."""
from pathlib import Path
import argparse
import importlib.util
import json
import sys
from contextlib import nullcontext

HERE=Path(__file__).resolve().parent
COMPACT=HERE.parent

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod

compiler=load('control_regions_geometry',COMPACT/'repeated_control/geometry/compile.py')
sys.path.insert(0,str(COMPACT/'operand_dispatch'))
runtime=load('control_regions_runtime',COMPACT/'operand_dispatch/runtime.py')
guard=load('control_regions_overflow',HERE/'overflow_region.py')
zero=load('control_regions_zero_pop',HERE/'zero_pop.py')
contexts=load('control_regions_zero_context',HERE/'zero_context.py')

def build(source,out,plan=None,groups=None,discover=False,overflow=None,zero_pop=False,zero_context=False):
    with runtime.installed(),guard.installed(overflow) if overflow else nullcontext([]) as guard_builders,zero.installed() if zero_pop else nullcontext([]) as builders,contexts.installed() if zero_context else nullcontext([]) as context_builders:
        result=compiler.measure(source,out,plan=plan,groups=groups,discover=discover)
    path=Path(out)/'metadata.json';data=json.loads(path.read_text())
    data.update(format='np-conp-control-region-complete-experiment-v1',
        generator_sha256=compiler.base.sha(Path(__file__)),
        overflow_lowering=overflow,
        zero_pop_lowering=zero_pop,
        zero_context_specialization=zero_context,
        source_proof='control_regions/PROOF.md',
        source_changed=not data['source_identical_to_284'],
        backend='operation-specific selectors with freshly derived zero-run dispatcher',
        review_status='unreviewed complete experiment; source and physical refinement require new review')
    compiler.base.dump(path,data)
    if overflow:
        compiler.base.dump(Path(out)/'overflow-guard.json',guard_builders[-1].overflow_guard_certificate)
    if zero_pop:
        compiler.base.dump(Path(out)/'zero-pop.json',builders[-1].zero_pop_certificate)
    if zero_context:
        compiler.base.dump(Path(out)/'zero-context.json',context_builders[-1].zero_context_certificate)
        data['contextual_tree_certificate_scope']='original context pass to zero-context input; zero-context specialization and cleanup to pre-control-grammar'
        compiler.base.dump(path,data)
    return data

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--plan',type=Path);p.add_argument('--groups',type=Path)
    p.add_argument('--overflow',choices=['native','borrow'])
    p.add_argument('--zero-pop',action='store_true')
    p.add_argument('--zero-context',action='store_true')
    p.add_argument('--discover',action='store_true');a=p.parse_args()
    m=build(a.source,a.out,plan=json.loads(a.plan.read_text()) if a.plan else None,
        groups=json.loads(a.groups.read_text()) if a.groups else None,discover=a.discover,overflow=a.overflow,zero_pop=a.zero_pop,zero_context=a.zero_context)
    print(json.dumps({k:m[k] for k in ('raw_states','states','event_states','registers','event_table_sha256')},indent=2))
