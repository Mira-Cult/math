"""Paid whole-controller experiment composing zero and neutral specialization."""
from pathlib import Path
import argparse
import importlib.util
import json

HERE=Path(__file__).resolve().parent


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value)
    return value


base=load('control_neutral_base',HERE/'measure.py')
neutral=load('control_neutral_pass',HERE/'neutral_context.py')


def build(out,plan=None,groups=None,discover=False):
    import contextual_tree
    cleanup=contextual_tree.apply
    with base.runtime.installed(),base.contexts.installed(),neutral.installed(cleanup) as builders:
        result=base.compiler.measure(HERE.parent/'phase_swap/source.py',out,
            plan=plan,groups=groups,discover=discover)
    builder=builders[-1];out=Path(out)
    base.compiler.base.dump(out/'zero-context.json',builder.zero_context_certificate)
    base.compiler.base.dump(out/'neutral-context.json',builder.neutral_context_certificate)
    metadata=json.loads((out/'metadata.json').read_text())
    metadata.update(format='np-conp-control-zero-neutral-experiment-v1',source_changed=False,
        generator_sha256=base.compiler.base.sha(Path(__file__)),
        source_proof='control_regions/PROOF.md',
        zero_context_specialization=True,neutral_context_specialization=True,
        contextual_tree_certificate_scope='original context to zero-context input, zero-context to neutral-context input, neutral-context to pre-control grammar',
        review_status='unreviewed complete experiment; new control and physical refinement review required')
    base.compiler.base.dump(out/'metadata.json',metadata)
    return metadata


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--plan',type=Path);p.add_argument('--groups',type=Path);p.add_argument('--discover',action='store_true')
    a=p.parse_args();m=build(a.out,plan=json.loads(a.plan.read_text()) if a.plan else None,
        groups=json.loads(a.groups.read_text()) if a.groups else None,discover=a.discover)
    print(json.dumps({k:m[k] for k in ('raw_states','states','event_states','registers','event_table_sha256')},indent=2))
