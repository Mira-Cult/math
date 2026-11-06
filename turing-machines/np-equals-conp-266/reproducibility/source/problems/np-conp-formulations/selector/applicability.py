"""Conservative, separately checked applicability adapters for pinned PR44 code.

The vendored files remain byte-identical. These adapters run only during source
analysis and selector construction, and never change the mathematical program.
"""
from contextlib import contextmanager
from copy import deepcopy
import ast
import hashlib
import json


def digest_rows(rows):
    data=[[q,read,*row] for (q,read),row in sorted(rows.items())]
    return hashlib.sha256(json.dumps(data,separators=(',',':')).encode()).hexdigest()


class TupleReturnAnalysis(ast.NodeTransformer):
    """Give tuple-call outputs lower bound zero while retaining every RHS use.

    This copy is used only by positivity and its read-before-assignment audit.
    Preserving the call as an expression retains argument division obligations
    and old-value reads before any output is assigned. It is never executed.
    """
    def visit_Assign(self,node):
        if (len(node.targets)==1 and isinstance(node.targets[0],ast.Tuple)
                and isinstance(node.value,ast.Call)):
            targets=node.targets[0].elts
            if not targets or any(not isinstance(x,ast.Name) for x in targets):
                raise ValueError('tuple-call targets must be names')
            return [ast.copy_location(ast.Expr(value=deepcopy(node.value)),node)]+[
                ast.copy_location(ast.Assign(targets=[deepcopy(x)],value=ast.Constant(value=0)),node)
                for x in targets]
        return self.generic_visit(node)


def tuple_positivity(original,function):
    transformed=ast.fix_missing_locations(TupleReturnAnalysis().visit(deepcopy(function)))
    result=original(transformed)
    result['tuple_call_outputs']='unknown naturals; lower bound zero'
    result['tuple_call_arguments']='retained before assignments in analysis-only AST'
    return result


def restore_dead_entries(builder):
    """Restore only complete, unreachable states removed by graph GC.

    Original rows are immutable. Every added state has neither rows nor an
    incoming edge in the original graph. Added rows are exactly the pinned
    register entry/index templates; the original selector validator then checks
    the entire enlarged runtime. The new selector keeps the original numbering.
    """
    import tm
    rows=builder.tm.states
    before={key:tuple(row) for key,row in rows.items()}
    old_states={q for q,_ in before}
    old_targets={row[2] for row in before.values()}
    expected={}
    for index,reg in enumerate(builder.registers.values()):
        for op,terminal in (('inc',reg.inc),('dec',reg.decnz)):
            expected[terminal,'0']=('1','R','1b.reg.prep_1')
            expected[terminal,'1']=('0','R',f'2b.reg.{index}.{op}')
            expected[f'2b.reg.{index}.{op}','0']=('0','R',f'2b.reg.{index-1}.{op}')
            expected[f'2b.reg.{index}.{op}','1']=('1','R',f'2b.reg.{index}.{op}')
    added={}
    for key,wanted in expected.items():
        if key in before:
            if before[key]!=wanted: raise ValueError(('modified inherited register row',key))
        else:
            q,_=key
            if q in old_states or q in old_targets:
                raise ValueError(('missing row is not a GC-dead complete state',key))
            added[key]=wanted
    for key,row in added.items(): rows[key]=tm.Transition(*row)
    after={key:tuple(row) for key,row in rows.items()}
    if any(after[key]!=row for key,row in before.items()):
        raise AssertionError('dead-entry extension changed original rows')
    record=dict(format='np-conp-dead-register-entry-extension-v1',
        before_named_sha256=digest_rows(before),after_named_sha256=digest_rows(after),
        original_rows=len(before),added_rows=[[q,r,*v] for (q,r),v in sorted(added.items())],
        added_states=sorted({q for q,_ in added}),register_order=list(builder.registers),
        old_incoming_to_added_states=0,
        equivalence='identical old-state trajectories before subsequent selector representation change')
    builder.dead_entry_extension=record
    return record


@contextmanager
def adapted_runtime():
    """Install scoped adapters and restore the original module globals always."""
    import positive,shared_selector
    original_positive=positive.positivity
    original_check=shared_selector.check_input
    def analyze(function):return tuple_positivity(original_positive,function)
    def check(builder):
        restore_dead_entries(builder)
        return original_check(builder)
    positive.positivity=analyze
    shared_selector.check_input=check
    try:yield
    finally:
        positive.positivity=original_positive
        shared_selector.check_input=original_check
