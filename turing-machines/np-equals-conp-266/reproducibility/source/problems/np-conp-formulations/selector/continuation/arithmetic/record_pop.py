"""Fuse an exact unary-record decoder block into one shared half per bit.

This new lowering preserves the published codec and source, including its
virtual zero tail. It emits only the inherited paid natural primitives.
"""
from contextlib import contextmanager
from pathlib import Path
import argparse
import ast
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
CONTINUATION = HERE.parent
sys.path.insert(0, str(CONTINUATION/'compiler'))
import build_live


def literal(node, value):
    return isinstance(node, ast.Constant) and type(node.value) is int and node.value == value


def match_pop(statements):
    if len(statements) < 3:
        return None
    reset, loop, final = statements[:3]
    if not (isinstance(reset, ast.Assign) and len(reset.targets) == 1
            and isinstance(reset.targets[0], ast.Name) and literal(reset.value, 0)
            and isinstance(loop, ast.While) and not loop.orelse
            and isinstance(loop.test, ast.BinOp) and isinstance(loop.test.op, ast.Mod)
            and isinstance(loop.test.left, ast.Name) and literal(loop.test.right, 2)
            and len(loop.body) == 2):
        return None
    count, stream = reset.targets[0].id, loop.test.left.id
    increment, halve = loop.body
    def half(node):
        return (isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name)
                and node.target.id == stream and isinstance(node.op, ast.FloorDiv)
                and literal(node.value, 2))
    if not (count != stream and isinstance(increment, ast.AugAssign)
            and isinstance(increment.target, ast.Name) and increment.target.id == count
            and isinstance(increment.op, ast.Add) and literal(increment.value, 1)
            and half(halve) and half(final)):
        return None
    return count, stream


class RecordPopMixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.record_pop_certificate = []

    def block(self, frame, statements, loops=()):
        code = []
        index = 0
        while index < len(statements):
            matched = match_pop(statements[index:])
            if matched is None:
                code += super().block(frame, [statements[index]], loops)
                index += 1
                continue
            count, stream = matched
            result, packed = self.variable(frame, count), self.variable(frame, stream)
            A, B, Q, R, C = self.micro
            label = self.fresh('unary_record')
            code += [self.clear(result), self.label(label, [
                self.move(A, packed), self.half_kernel(), self.move(packed, Q),
                [R.decnz, [result.inc, 'continue_'+label]]])]
            self.record_pop_certificate.append(dict(function=frame['name'],
                line=statements[index].lineno, count=count, stream=stream,
                contract='consume low 1^a0; output count=a and remaining suffix; zero tail allowed',
                kernel='inherited half_kernel', event_free=True))
            index += 3
        return code


@contextmanager
def installed(base=None):
    original = build_live.HalfPairBuilder
    parent = original if base is None else base
    class RecordPopBuilder(RecordPopMixin, parent):
        pass
    build_live.HalfPairBuilder = RecordPopBuilder
    try:
        yield RecordPopBuilder
    finally:
        build_live.HalfPairBuilder = original


def construct(source, **kwargs):
    with installed():
        return build_live.construct(source, **kwargs)


def build(source, out, **kwargs):
    captured = []
    with installed() as parent:
        class Capture(parent):
            def __init__(self, *args, **options):
                super().__init__(*args, **options)
                captured.append(self)
        build_live.HalfPairBuilder = Capture
        metadata = build_live.build(out, source, **kwargs)
    assert len(captured) == 1
    record = dict(format='np-conp-unary-record-pop-v1',
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        sites=captured[0].record_pop_certificate,
        semantic_status='new guarded lowering; proof and independent review separate')
    (Path(out)/'record-pop.json').write_text(json.dumps(record, sort_keys=True, indent=2)+'\n')
    return metadata


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=CONTINUATION/'source/blank_incremental.py')
    parser.add_argument('--out', type=Path, required=True)
    args=parser.parse_args()
    result=build(args.source,args.out)
    print(json.dumps({key:result[key] for key in ('event_states','states','raw_states','registers','profile','event_table_sha256')},indent=2))
