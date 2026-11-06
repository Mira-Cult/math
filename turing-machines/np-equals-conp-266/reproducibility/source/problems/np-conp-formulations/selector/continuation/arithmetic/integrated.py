"""Complete composition of separately proved arithmetic compiler changes."""
from pathlib import Path
from contextlib import contextmanager
import argparse
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
CONTINUATION=HERE.parent
sys.path[:0]=[str(HERE),str(CONTINUATION/'compiler')]
import build_live
sys.path.insert(0,str(HERE/'compiler'))
from lowerings import ArithmeticBuilder
from record_pop import RecordPopMixin
from lookup import LookupMixin
from half_kernel import PairHalfMixin


@contextmanager
def installed(*,affine=True,pop=True,lookup=True,pair_half=False,options=None):
    original=build_live.HalfPairBuilder
    bases=[]
    if pair_half:bases.append(PairHalfMixin)
    if lookup:bases.append(LookupMixin)
    if pop:bases.append(RecordPopMixin)
    bases.append(ArithmeticBuilder if affine else original)
    Parent=type('IntegratedArithmetic',tuple(bases),{})
    instances=[]
    class Capture(Parent):
        def __init__(self,*args,**kwargs):
            if options:kwargs.update(options)
            super().__init__(*args,**kwargs)
            instances.append(self)
    build_live.HalfPairBuilder=Capture
    try:
        yield instances
    finally:
        build_live.HalfPairBuilder=original


def construct(source,**options):
    with installed(**options):
        return build_live.construct(source)


def build(source,out,**options):
    with installed(**options) as instances:
        metadata=build_live.build(out,source)
    assert len(instances)==1
    b=instances[0]
    metadata['format']='np-conp-integrated-arithmetic-v1'
    metadata['new_options']=dict(affine=True,pop=True,lookup=True,pair_half=False)|options
    metadata['new_producers']={p:hashlib.sha256((HERE/p).read_bytes()).hexdigest()
        for p in ('integrated.py','record_pop.py','lookup.py','half_kernel.py','compiler/lowerings.py')}
    metadata['proof_status']='new complete compilation; mathematical proof and independent review separate'
    for name,data in [
        ('metadata.json',metadata),
        ('new-arithmetic.json',getattr(b,'arithmetic_certificate',[])),
        ('record-pop.json',getattr(b,'record_pop_certificate',[])),
        ('lookup.json',getattr(b,'lookup_certificate',[]))]:
        (Path(out)/name).write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    return metadata


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=HERE/'source/forced_relative.py')
    p.add_argument('--out',type=Path,required=True);p.add_argument('--no-affine',action='store_true')
    p.add_argument('--no-pop',action='store_true');p.add_argument('--no-lookup',action='store_true')
    p.add_argument('--pair-half',action='store_true')
    a=p.parse_args();r=build(a.source,a.out,affine=not a.no_affine,pop=not a.no_pop,lookup=not a.no_lookup,pair_half=a.pair_half)
    print(json.dumps({k:r[k] for k in ('event_states','states','raw_states','registers','profile','event_table_sha256')},indent=2))
