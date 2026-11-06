"""Replay a fresh all-preimage completion for the control-mode selector."""
from pathlib import Path
import argparse
import importlib.util
import json
import re

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('operand_completion',HERE.parent/'binary_phase/coordinator/select.py')
completion=importlib.util.module_from_spec(spec);spec.loader.exec_module(completion)
completion.SOURCE=HERE.parent/'phase_swap/source.py'
old_category=completion.categories.category


def category(name):
    if name.startswith('repeat.dispatch.'):return 'return delimiter scan'
    if re.fullmatch(r'2b\.reg\.\d+\.(inc|dec)',name):return 'operation-specific operand selectors'
    return old_category(name)


completion.categories.category=category


def select(parent,out,plan):
    result=completion.build(parent,out,plan)
    path=Path(out)/'metadata.json';m=json.loads(path.read_text())
    m.update(format='np-conp-control-mode-selector-selected-v1',source_changed=False,
        source_change='exact reviewed284 source; selector operation kind in control, one-zero preparation, six-zero return delimiter',
        source_theorem='../../PROOF.md and ../../../phase_swap/COMPOSITION.md',
        event_trace_relation='same source events; new physical timing; marked ingress one transition before B exit',
        generator_sha256=completion.sha(Path(__file__)),
        inherited_completion_generator_sha256=completion.sha(Path(completion.__file__)),
        independent_review='pending; no predecessor acceptance inherited onto changed literal bytes')
    completion.dump(path,m)
    path=Path(out)/'domain.json';domain=json.loads(path.read_text())
    domain['premise']='The exact unchanged source and freshly generated storage/control certificates establish the one-zero unary-bank boundary. The restored INC/DECNZ selectors and unchanged native HALF segment contracts exclude these five named reads. Every raw preimage is checked; membership in totalization metadata alone is not a proof. See ../../PROOF.md.'
    completion.dump(path,domain)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('parent','out','plan'):p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();print(json.dumps(select(a.parent,a.out,a.plan),indent=2))
