"""Normalized marker/payload parser with direct HALF phase control."""
from contextlib import contextmanager
from pathlib import Path
import argparse
import ast
import json
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import build_skip
from build_skip import build_coalesced,lower_half


def match_marker(statements):
    if len(statements)<2:return None
    loop,final=statements[:2]
    if not isinstance(loop,ast.While) or loop.orelse or not loop.body:return None
    test=loop.test
    if not (isinstance(test,ast.BinOp) and isinstance(test.op,ast.Mod) and isinstance(test.left,ast.Name)
            and isinstance(test.right,ast.Constant) and type(test.right.value) is int and test.right.value==2):return None
    name=test.left.id
    def half(n):return isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id==name and isinstance(n.op,ast.FloorDiv) and isinstance(n.value,ast.Constant) and type(n.value.value) is int and n.value.value==2
    if not half(loop.body[0]) or not half(final):return None
    body=loop.body[1:]
    if any(isinstance(n,(ast.Call,ast.Return,ast.Break,ast.Continue)) for st in body for n in ast.walk(st)):return None
    return name,body


@contextmanager
def installed():
    with build_skip.installed():
        original=lower_half.NativeHalfMixin.block
        def block(self,frame,statements,loops=()):
            code=[];index=0
            while index<len(statements):
                matched=match_marker(statements[index:])
                if matched is not None:
                    name,body=matched;source=self.variable(frame,name);label=self.fresh('native_marker_phase')
                    code += [self.label(label,[self.half_operation(source),[self.block(frame,body,loops),'continue_'+label]])]
                    self.native_half_certificate.append(dict(function=frame['name'],line=statements[index].lineno,
                        kind='marker-phase-loop',source=str(source),
                        contract='HALF consumes successful marker before body and consumes failed terminator before exit'))
                    index+=2
                else:
                    end=index+1
                    while end<len(statements) and match_marker(statements[end:]) is None:end+=1
                    code+=original(self,frame,statements[index:end],loops);index=end
            return code
        lower_half.NativeHalfMixin.block=block
        try:yield
        finally:lower_half.NativeHalfMixin.block=original


def build(out,*,discover=False,plan=None,groups=None):
    with installed():
        if discover:return build_coalesced.build(out,HERE/'source.py',weak=True,groups=groups)
        if plan is None:return build_coalesced.build(out,HERE/'source.py',weak=False,groups=groups)
        with build_coalesced.weak_grammar.installed(json.loads(Path(plan).read_text())):
            return build_coalesced.build(out,HERE/'source.py',weak=False,groups=groups)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--discover',action='store_true');p.add_argument('--plan',type=Path);p.add_argument('--groups',type=Path);a=p.parse_args()
    m=build(a.out,discover=a.discover,plan=a.plan,groups=json.loads(a.groups.read_text()) if a.groups else None)
    print(json.dumps({k:m[k] for k in ('raw_states','states','event_states','registers','event_table_sha256')},indent=2))
