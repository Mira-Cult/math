"""Complete measured integration; discovery and fixed replay are distinct modes."""
from contextlib import ExitStack, contextmanager
from pathlib import Path
import argparse
import importlib.util
import json
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
COMPACT=ROOT.parent
sys.path.insert(0,str(COMPACT/'binary_phase/control/parser'))
import build_parser
from build_parser import build_coalesced


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


@contextmanager
def installed(*,clock=False,action=False,seed=False,consume=False):
    with ExitStack() as stack:
        if action:
            region=load('npconp_transfer_action',ROOT/'physical/region.py')
            stack.enter_context(region.installed(whole=True))
        else:
            stack.enter_context(build_parser.installed())
        if clock:
            region=load('npconp_transfer_clock',ROOT/'control/clock_region.py')
            stack.enter_context(region.installed(borrow=True))
        if seed:
            sys.path.insert(0,str(ROOT/'control'))
            region=load('npconp_transfer_seed',ROOT/'control/seed_region.py')
            stack.enter_context(region.installed())
        if consume:
            region=load('npconp_transfer_consume',HERE/'consume_guard.py')
            stack.enter_context(region.installed())
        yield


def build(source,out,*,clock=False,action=False,seed=False,consume=False,discover=False,plan=None,groups=None):
    with installed(clock=clock,action=action,seed=seed,consume=consume):
        if plan is not None:
            with build_coalesced.weak_grammar.installed(json.loads(plan.read_text())):
                return build_coalesced.build(out,source,weak=False,groups=groups)
        return build_coalesced.build(out,source,weak=discover,groups=groups)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--clock',action='store_true')
    p.add_argument('--action',action='store_true')
    p.add_argument('--seed',action='store_true')
    p.add_argument('--consume',action='store_true')
    p.add_argument('--discover',action='store_true')
    p.add_argument('--plan',type=Path)
    p.add_argument('--groups',type=Path)
    a=p.parse_args()
    if a.out.exists():raise ValueError('fresh output directory required')
    m=build(a.source,a.out,clock=a.clock,action=a.action,seed=a.seed,consume=a.consume,discover=a.discover,plan=a.plan,
            groups=json.loads(a.groups.read_text()) if a.groups else None)
    print(json.dumps({k:m[k] for k in ('raw_states','states','event_states','registers','profile','event_table_sha256')},indent=2))
