"""Fixed all-preimage completion with accurate control-region provenance."""
from pathlib import Path
import argparse
import importlib.util
import json

HERE=Path(__file__).resolve().parent
COMPACT=HERE.parent
spec=importlib.util.spec_from_file_location('control_region_completion',COMPACT/'operand_dispatch/select.py')
previous=importlib.util.module_from_spec(spec);spec.loader.exec_module(previous)
completion=previous.completion


def select(source,parent,out,plan):
    source,parent,out,plan=map(Path,(source,parent,out,plan))
    completion.SOURCE=source
    result=completion.build(parent,out,plan)
    parent_metadata=json.loads((parent/'metadata.json').read_text())
    metadata=json.loads((out/'metadata.json').read_text())
    unchanged=completion.sha(source)==completion.sha(COMPACT/'phase_swap/source.py')
    if unchanged:
        change='exact predecessor source'
    elif source.stem=='reuse_clock_roles':
        change='proved post-reference phase ownership: reuse e,n for candidate description and numerical clock'
    elif source.stem=='reuse_description_time':
        change='proved post-reference phase ownership: normalize candidate description and time carriers'
    elif source.stem.startswith('equality_'):
        change='direct equality comparison of reference bit and final candidate state; dead-value guard consumption where explicit'
    else:
        change='source transformation and fresh lowering stated in control_regions/PROOF.md'
    if parent_metadata.get('zero_context_specialization'):
        change+='; occurrence-specific proved-zero tests eliminated'
    if parent_metadata.get('zero_pop_lowering'):
        change+='; proved-zero accumulator at both final record pops'
    if 'geometry_discovery' in json.loads((parent/'weak-grammar-plan.json').read_text()):
        change+='; fixed full-control geometry preserving every retained branch and event'
    metadata.update(format='np-conp-control-region-selected-v1',source_changed=not unchanged,
        source_name=source.resolve().relative_to(COMPACT).as_posix(),
        source_change=change,
        source_theorem='../../PROOF.md and ../../../phase_swap/COMPOSITION.md',
        event_trace_relation='same source comparison bits and ordered events; physical timing changes; marked ingress one step before B exit',
        generator_sha256=completion.sha(Path(__file__)),
        inherited_completion_generator_sha256=completion.sha(Path(completion.__file__)),
        independent_review='pending; no predecessor acceptance inherited onto changed literal bytes')
    completion.dump(out/'metadata.json',metadata)
    domain=json.loads((out/'domain.json').read_text())
    domain['premise']='The source equivalence proof and fresh storage/control certificates establish the one-zero unary-bank boundary. The existing INC/DECNZ and native HALF segment contracts exclude the five named reads. All raw quotient preimages are checked; membership in totalization metadata alone is not a proof. See ../../PROOF.md.'
    completion.dump(out/'domain.json',domain)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('source','parent','out','plan'):p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();print(json.dumps(select(a.source,a.parent,a.out,a.plan),indent=2))
