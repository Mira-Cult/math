"""Compile whole skipped records directly as native HALF loops, without search by default."""
from contextlib import contextmanager
from pathlib import Path
import argparse
import ast
import json
import sys

HERE=Path(__file__).resolve().parent
COMPACT=HERE.parents[1]
sys.path[:0]=[str(COMPACT/'compiler/native')]
import build_coalesced
import lower_half
import live_registers


def match_skip(statements):
    if len(statements)<2: return None
    loop, final=statements[:2]
    if not isinstance(loop, ast.While) or loop.orelse: return None
    test=loop.test
    if not (isinstance(test,ast.BinOp) and isinstance(test.op,ast.Mod)
            and isinstance(test.left,ast.Name) and isinstance(test.right,ast.Constant)
            and type(test.right.value) is int and test.right.value==2): return None
    name=test.left.id
    def half(node):
        return (isinstance(node,ast.AugAssign) and isinstance(node.target,ast.Name)
                and node.target.id==name and isinstance(node.op,ast.FloorDiv)
                and isinstance(node.value,ast.Constant) and type(node.value.value) is int
                and node.value.value==2)
    if len(loop.body)==1 and half(loop.body[0]) and half(final): return name
    return None


def match_parity_branch(statements):
    if len(statements)<2: return None
    branch, final=statements[:2]
    if not isinstance(branch,ast.If): return None
    test=branch.test
    if not (isinstance(test,ast.BinOp) and isinstance(test.op,ast.Mod)
            and isinstance(test.left,ast.Name) and isinstance(test.right,ast.Constant)
            and type(test.right.value) is int and test.right.value==2): return None
    name=test.left.id
    if not (isinstance(final,ast.AugAssign) and isinstance(final.target,ast.Name)
            and final.target.id==name and isinstance(final.op,ast.FloorDiv)
            and isinstance(final.value,ast.Constant) and type(final.value.value) is int
            and final.value.value==2): return None
    # Moving HALF before either branch is safe only when both branches do
    # not inspect or change that operand, and have no nonlocal exit.
    if any(isinstance(n,ast.Name) and n.id==name or isinstance(n,(ast.Return,ast.Break,ast.Continue,ast.Call))
           for node in branch.body+branch.orelse for n in ast.walk(node)): return None
    return name,branch.body,branch.orelse


@contextmanager
def installed(*, fused=False, fused_push=False):
    original=lower_half.NativeHalfMixin.block
    original_interference=live_registers.interference
    extra_edges={}
    def interference(function,registers,returns,retained_resets,reuse_returns):
        cfg,graph=original_interference(function,registers,returns,retained_resets,reuse_returns)
        added=[]
        if fused:
            for reset in ast.walk(function):
                if not isinstance(reset,ast.Assign): continue
                # Identify only the actual expanded four-phase sites recorded
                # by the block lowering; the entry source live set is a
                # conservative lifetime extension for the early write clear.
                for line,write in extra_edges.get(function.name,[]):
                    if reset.lineno!=line: continue
                    entries=[n for n in cfg['nodes'] if n['line']==line]
                    live=set().union(*(set(n['live_in'])|set(n['live_out']) for n in entries))
                    for other in live:
                        if other!=write and other in graph and write in graph:
                            graph[write].add(other);graph[other].add(write)
                            added.append([write,other])
        if added:cfg['lowering_lifetime_edges']=sorted(added)
        return cfg,graph
    def block(self,frame,statements,loops=()):
        code=[]; index=0
        while index<len(statements):
            name=match_skip(statements[index:])
            parity=match_parity_branch(statements[index:])
            pop=lower_half.match_pop(statements[index:]) if fused else None
            packed=None
            if pop is not None and len(statements)-index>=6:
                count,stream=pop
                pair=self.divrem_assignment(statements[index+3])
                turn=match_parity_branch(statements[index+4:])
                if (pair is not None and isinstance(pair[2],ast.Constant) and type(pair[2].value) is int and pair[2].value==2
                        and pair[0][1].id==pair[1].id==count and turn is not None and turn[0]==count and not turn[2]):
                    output=pair[0][0].id
                    if len({output,count,stream})==3 and not any(isinstance(n,ast.Name) and n.id in {count,stream,output}
                        for node in turn[1] for n in ast.walk(node)):
                        packed=(count,stream,output,turn[1])
            pushing=None
            if packed is not None and fused_push and len(statements)-index>=7:
                count,stream,output,turn_body=packed
                push=statements[index+6]
                if isinstance(push,ast.Assign) and len(push.targets)==1 and isinstance(push.targets[0],ast.Name):
                    left=push.targets[0].id
                    expected=ast.parse(f'{left} = 2 * {left} + {output}').body[0]
                    if ast.dump(push,include_attributes=False)==ast.dump(expected,include_attributes=False) and left not in (count,stream,output):
                        cfg=live_registers.function_cfg(self.functions[frame['name']],tuple('ret'+str(i) for i in range(len(frame['returns']))))
                        outputs=[n for n in cfg['nodes'] if n['line']==push.lineno and n['kind']=='assign']
                        if len(outputs)==1 and output not in outputs[0]['live_out']:
                            pushing=left
            if pushing is not None:
                count,stream,output,turn_body=packed
                result=self.variable(frame,count);source=self.variable(frame,stream);left=self.variable(frame,pushing)
                swap=self.block(frame,turn_body,loops)
                doubling=self.block(frame,ast.parse(f'{pushing} *= 2').body,loops)
                loop=self.fresh('record_four_phase');done=self.fresh('record_four_done')
                half=self.half_operation(source)
                code += [self.clear(result),self.label(done,[self.label(loop,[
                    [half,[
                        [half,[
                            [half,[
                                [half,[result.inc,'continue_'+loop]],
                                swap,doubling,left.inc,'break_'+done]],
                            swap,doubling,'break_'+done]],
                        doubling,left.inc,'break_'+done]],
                    doubling,'break_'+done])])]
                self.native_half_certificate.append(dict(function=frame['name'],line=statements[index].lineno,
                    kind='four-phase-record-push',source=str(source),next_state=str(result),left=str(left),
                    elided_write=output,write_dead_after_line=statements[index+6].lineno,
                    contract='consume 1^a0; next=floor(a/4); turn body iff floor(a/2)%2; left=2*selected_left+a%2'))
                index+=7
            elif packed is not None:
                count,stream,output,turn_body=packed
                extra_edges.setdefault(frame['name'],[]).append((statements[index].lineno,output))
                result=self.variable(frame,count); source=self.variable(frame,stream); write=self.variable(frame,output)
                swap=self.block(frame,turn_body,loops)
                loop=self.fresh('record_four_phase'); done=self.fresh('record_four_done')
                half=self.half_operation(source)
                # Each success consumes a one; every failure consumes exactly
                # the next zero.  The residue is held by the finite path.
                code += [self.clear(result),self.clear(write),self.label(done,[self.label(loop,[
                    [half,[
                        [half,[
                            [half,[
                                [half,[result.inc,'continue_'+loop]],
                                write.inc,swap,'break_'+done]],
                            swap,'break_'+done]],
                        write.inc,'break_'+done]],
                    'break_'+done])])]
                self.native_half_certificate.append(dict(function=frame['name'],line=statements[index].lineno,
                    kind='four-phase-record',source=str(source),next_state=str(result),write=str(write),
                    contract='consume 1^a0; next=floor(a/4), write=a%2; run turn body iff floor(a/2)%2'))
                index+=6
            elif parity is not None:
                operand,yes,no=parity
                source=self.variable(frame,operand)
                true=self.block(frame,yes,loops)
                false=self.block(frame,no,loops)
                if false:
                    raise ValueError('experiment has no false-body lowering yet')
                code += [[self.half_operation(source),true]]
                self.native_half_certificate.append(dict(function=frame['name'],line=statements[index].lineno,
                    kind='parity-branch',source=str(source)))
                index+=2
            elif name is not None:
                source=self.variable(frame,name)
                label=self.fresh('native_skip_record')
                code += [self.label(label,[self.half_operation(source),'continue_'+label])]
                self.native_half_certificate.append(dict(function=frame['name'],line=statements[index].lineno,
                    kind='skip-record',source=str(source)))
                index+=2
            else:
                # Preserve the inherited three-node POP recognizer by sending
                # maximal spans up to the next newly recognized skip.
                end=index+1
                while end<len(statements) and match_skip(statements[end:]) is None and match_parity_branch(statements[end:]) is None and (not fused or lower_half.match_pop(statements[end:]) is None): end+=1
                code += original(self,frame,statements[index:end],loops)
                index=end
        return code
    lower_half.NativeHalfMixin.block=block
    live_registers.interference=interference
    try: yield
    finally:
        lower_half.NativeHalfMixin.block=original
        live_registers.interference=original_interference


def build(out, *, source=None, fused=False, fused_push=False, discover=False, plan=None, groups=None):
    source=source or HERE/'source_skip.py'
    with installed(fused=fused,fused_push=fused_push):
        if discover:
            result=build_coalesced.build(out,source,weak=True,groups=groups)
        elif plan is None:
            result=build_coalesced.build(out,source,weak=False,groups=groups)
        else:
            with build_coalesced.weak_grammar.installed(json.loads(Path(plan).read_text())):
                result=build_coalesced.build(out,source,weak=False,groups=groups)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--discover',action='store_true')
    p.add_argument('--fused',action='store_true')
    p.add_argument('--fused-push',action='store_true')
    p.add_argument('--source',type=Path)
    p.add_argument('--plan',type=Path)
    p.add_argument('--groups',type=Path)
    a=p.parse_args()
    m=build(a.out,source=a.source,fused=a.fused,fused_push=a.fused_push,discover=a.discover,plan=a.plan,
        groups=json.loads(a.groups.read_text()) if a.groups else None)
    print(json.dumps({k:m[k] for k in ('raw_states','states','event_states','registers','event_table_sha256')},indent=2))
