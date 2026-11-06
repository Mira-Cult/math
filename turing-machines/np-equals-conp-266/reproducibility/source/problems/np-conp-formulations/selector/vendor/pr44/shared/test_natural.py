#!/usr/bin/env python3
"""Independent source/tree audit for the proposed natural-number compiler.

This file reads compiled cons-tree nodes but imports no production semantic
helper.  It interprets register primitives and the binary return-path protocol
directly.  It is an audit, not a compilation stage or an uncounted runtime.
"""
from __future__ import annotations

import ast
from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json
import sys


_HERE = Path(__file__).resolve().parent
CODE = next(path for path in (_HERE, _HERE.parent / 'code',
                            _HERE / 'math-wip/problems/np-conp-beeper/code')
            if (path / 'natural.py').is_file())
sys.path.insert(0, str(CODE))
from natural import NaturalBuilder


class AuditLimit(Exception):
    pass


class TreeVM:
    """Interpret generated unary primitives with independent return paths.

    The control tape has prefix 110.  Sequence descents append the selected
    branch, with zero used beyond the finite written prefix.  A successful
    primitive erases trailing ones and flips the nearest zero.  A failed
    DECNZ skips one extra zero before doing that.  A loop continuation clears
    the specified number of right-branch ones and all trailing zeros.
    """
    def __init__(self, builder):
        self.nodes = tuple(tuple(s.seq) for s in builder.sequences)
        names = [s.name for s in builder.sequences]
        self.root = names.index('main().0')
        self.registers = defaultdict(int)
        self.path = (1, 1, 0)
        self.steps = 0
        self.beep_records = []
        self.resolve_cache = {}

    def resolve(self, path):
        assert path[:2] == (1, 1), ('missing root sentinel', path)
        if len(path) < 3:
            path += (0,) * (3 - len(path))
        # The backend's root returns to the whole program on completion.
        if path[:3] == (1, 1, 1):
            path = (1, 1, 0)
        if path in self.resolve_cache:
            return self.resolve_cache[path]
        original = path
        digits = list(path)
        cursor = 3
        node = self.root
        while type(node) is int:
            pair = self.nodes[node]
            assert len(pair) == 2, ('not cons', node, pair)
            if cursor == len(digits):
                digits.append(0)
            node = pair[digits[cursor]]
            cursor += 1
        assert cursor == len(digits), ('extra control path', node, digits, cursor)
        result = node, tuple(digits)
        self.resolve_cache[original] = result
        return result

    @staticmethod
    def return_path(path, skipped_zeroes):
        # Initial sentinel ones at indices zero and one cannot be consumed.
        for index in range(len(path) - 1, 1, -1):
            if path[index] == 0:
                if skipped_zeroes:
                    skipped_zeroes -= 1
                else:
                    return path[:index] + (1,)
        raise AssertionError(('return beyond root', path, skipped_zeroes))

    @staticmethod
    def continue_path(path, cleared_ones):
        for index in range(len(path) - 1, 0, -1):
            if path[index] == 1:
                if cleared_ones:
                    cleared_ones -= 1
                else:
                    return path[:index + 1]
        raise AssertionError(('continue beyond root', path, cleared_ones))

    def step(self):
        leaf, path = self.resolve(self.path)
        self.steps += 1
        if leaf == 'beep':
            self.beep_records.append((self.steps, dict(self.registers)))
            self.path = self.return_path(path, 0)
        elif leaf.startswith('_break.'):
            self.path = self.return_path(path, int(leaf.split('.')[1]))
        elif leaf.startswith('_continue.'):
            self.path = self.continue_path(path, int(leaf.split('.')[1]))
        elif leaf.startswith('3.'):
            register, operation = leaf[2:].rsplit('.', 1)
            value = self.registers[register]
            if operation == 'inc':
                self.registers[register] = value + 1
                self.path = self.return_path(path, 0)
            elif operation == 'decnz':
                if value:
                    self.registers[register] = value - 1
                self.path = self.return_path(path, int(value == 0))
            else:
                raise AssertionError(('unexpected register primitive', leaf))
        else:
            raise AssertionError(('unexpected leaf', leaf))

    def until_beeps(self, count, limit=10_000_000):
        while len(self.beep_records) < count:
            if self.steps >= limit:
                raise AuditLimit(('tree primitive limit', limit, self.path))
            self.step()
        return self.beep_records


class Returned(Exception):
    def __init__(self, values):
        self.values = values


class BreakLoop(Exception):
    pass


class ContinueLoop(Exception):
    pass


class SourceVM:
    """Separately written mathematical-natural AST evaluator.

    Uses no compiler arithmetic/label/temp helpers.  Division by zero and
    saturating subtraction are interpreted explicitly, and Boolean operators
    return bits with short-circuit control as the language contract states.
    """
    def __init__(self, text, limit=1_000_000, beep_limit=None):
        self.functions = {f.name: f for f in ast.parse(text).body
                          if isinstance(f, ast.FunctionDef)}
        self.active = []
        self.last_frames = {}
        self.steps = 0
        self.limit = limit
        self.beep_limit = beep_limit
        self.beeps = []

    def tick(self):
        self.steps += 1
        if self.steps > self.limit:
            raise AuditLimit(('source limit', self.limit))

    def expr(self, node, env):
        self.tick()
        if isinstance(node, ast.Constant):
            return int(node.value)
        if isinstance(node, ast.Name):
            return env[node.id]
        if isinstance(node, (ast.Tuple, ast.List)):
            return tuple(self.expr(x, env) for x in node.elts)
        if isinstance(node, ast.Call):
            values = self.call(node.func.id, tuple(self.expr(x, env) for x in node.args))
            return values[0] if len(values) == 1 else values
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return int(not self.expr(node.operand, env))
        if isinstance(node, ast.BoolOp):
            value = int(bool(self.expr(node.values[0], env)))
            for child in node.values[1:]:
                if isinstance(node.op, ast.And) and not value:
                    break
                if isinstance(node.op, ast.Or) and value:
                    break
                value = int(bool(self.expr(child, env)))
            return value
        if isinstance(node, ast.BinOp):
            a, b = self.expr(node.left, env), self.expr(node.right, env)
            if isinstance(node.op, ast.Add): return a + b
            if isinstance(node.op, ast.Sub): return max(a - b, 0)
            if isinstance(node.op, ast.Mult): return a * b
            if isinstance(node.op, ast.FloorDiv): return a // b if b else 0
            if isinstance(node.op, ast.Mod): return a % b if b else a
            if isinstance(node.op, ast.Pow): return a ** b
        if isinstance(node, ast.Compare):
            a, b = self.expr(node.left, env), self.expr(node.comparators[0], env)
            op = node.ops[0]
            if isinstance(op, ast.Eq): return int(a == b)
            if isinstance(op, ast.NotEq): return int(a != b)
            if isinstance(op, ast.Lt): return int(a < b)
            if isinstance(op, ast.LtE): return int(a <= b)
            if isinstance(op, ast.Gt): return int(a > b)
            if isinstance(op, ast.GtE): return int(a >= b)
        raise AssertionError(('unsupported reference expression', ast.dump(node)))

    def block(self, statements, env):
        for node in statements:
            self.tick()
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant):
                continue
            if isinstance(node, ast.Assign):
                value = self.expr(node.value, env)
                target = node.targets[0]
                if isinstance(target, ast.Tuple):
                    for name, item in zip(target.elts, value):
                        env[name.id] = item
                else:
                    env[target.id] = value
            elif isinstance(node, ast.AugAssign):
                synthetic = ast.BinOp(left=ast.Name(id=node.target.id), op=node.op,
                                      right=node.value)
                env[node.target.id] = self.expr(synthetic, env)
            elif isinstance(node, ast.If):
                self.block(node.body if self.expr(node.test, env) else node.orelse, env)
            elif isinstance(node, ast.While):
                while self.expr(node.test, env):
                    try:
                        self.block(node.body, env)
                    except BreakLoop:
                        break
                    except ContinueLoop:
                        continue
            elif isinstance(node, ast.Break):
                raise BreakLoop
            elif isinstance(node, ast.Continue):
                raise ContinueLoop
            elif isinstance(node, ast.Return):
                value = self.expr(node.value, env)
                raise Returned(value if type(value) is tuple else (value,))
            elif isinstance(node, ast.Expr) and node.value.func.id == 'beep':
                snapshot = {}
                for name, frame in self.last_frames.items():
                    snapshot.update({name + '.' + key: value for key, value in frame.items()})
                self.beeps.append(snapshot)
                if self.beep_limit is not None and len(self.beeps) >= self.beep_limit:
                    raise AuditLimit(('beep limit reached', self.beep_limit))
            else:
                raise AssertionError(('unsupported reference statement', ast.dump(node)))

    def call(self, name, args):
        function = self.functions[name]
        env = defaultdict(int, zip((a.arg for a in function.args.args), args))
        self.last_frames[name] = env
        self.active.append(name)
        try:
            self.block(function.body, env)
        except Returned as result:
            return result.values
        finally:
            self.active.pop()
        arities = {len(n.value.elts) if isinstance(n.value, ast.Tuple) else 1
                   for n in ast.walk(function) if isinstance(n, ast.Return)}
        return (0,) * next(iter(arities), 0)


def compile_and_run(text, entry, args, share=False, beep_count=1, limit=10_000_000):
    builder = NaturalBuilder(text, entry=entry, entry_args=args, share=share)
    builder.main()
    assert_factorable_entries_closed(builder)
    builder.build_tree()
    vm = TreeVM(builder)
    vm.until_beeps(beep_count, limit)
    return vm, builder


def assert_factorable_entries_closed(builder):
    """Check the structural invariant needed by the optional sharing pass.

    A break needs k zero edges and a continuation k one edges locally; negative
    requirements mean extra local edges were already supplied.  Every entry
    of a factorable (>2) sequence must be closed under both kinds of jump.
    This audit does not rely on register values or a bounded execution trace.
    """
    memo = {}
    absent = -10**9  # no reference of that kind in this finite syntax subtree

    def demand(value):
        if type(value) is int:
            if value in memo:
                return memo[value]
            children = builder.sequences[value].seq
            result = (absent, absent)
            for index, child in enumerate(children):
                zeros = int(index < len(children) - 1)
                ones = index
                b, c = demand(child)
                result = (max(result[0], b - zeros), max(result[1], c - ones))
            memo[value] = result
            return result
        if value.startswith('_break.'):
            return int(value.split('.')[1]), absent
        if value.startswith('_continue.'):
            return absent, int(value.split('.')[1])
        if value.endswith('.decnz'):
            return 1, absent
        if value == 'beep' or value.endswith('.inc'):
            return 0, absent
        raise AssertionError(('unrecognized primitive in closure audit', value))

    root = next(i for i, s in enumerate(builder.sequences) if s.name == 'main().0')
    todo, seen = [root], set()
    while todo:
        index = todo.pop()
        if index in seen:
            continue
        seen.add(index)
        children = builder.sequences[index].seq
        for child in children:
            if len(children) > 2:
                assert max(demand(child)) <= 0, ('factorable entry has escaping jump',
                                               index, child, demand(child))
            if type(child) is int:
                todo.append(child)


def check_fixture(text, entry, args, share=False):
    source = SourceVM(text)
    expected = source.call(entry, args)
    vm, builder = compile_and_run(text, entry, args, share=share,
                                 beep_count=len(source.beeps) + 1)
    final = vm.beep_records[-1][1]
    actual = tuple(final.get(f'{entry}.ret{i}', 0) for i in range(len(expected)))
    assert actual == expected, {'entry': entry, 'args': args, 'share': share,
                                'expected': expected, 'actual': actual, 'source': text}
    dirty = {k: v for k, v in final.items()
             if v and ('.tmp' in k or k == 'scratch.copy')}
    assert not dirty, ('dirty temporary after return', dirty, text, args)
    for reference, (_, observation) in zip(source.beeps, vm.beep_records):
        for name, value in reference.items():
            assert observation.get(name, 0) == value, ('beep ordering/register mismatch',
                                                      name, value, observation.get(name), text)
    return vm.steps, len(builder.registers)


ARITHMETIC = '''
def f(a, b):
    plus, minus, times = a+b, a-b, a*b
    quotient, remainder = a//b, a%b
    eq, ne, lt, le, gt, ge = a==b, a!=b, a<b, a<=b, a>b, a>=b
    return plus, minus, times, quotient, remainder, eq, ne, lt, le, gt, ge
'''


FLOW = '''
def f(a, b):
    total, outer = 0, 0
    while outer < a:
        outer += 1
        inner = b
        while inner:
            inner -= 1
            if inner == 2:
                continue
            if outer == 2 and inner == 1:
                break
            if outer == 3 and inner == 0:
                return total, outer, inner
            total += outer + inner
        if outer == 4:
            break
    return total, outer, inner
'''


CALLS = '''
def bump(x):
    local = x + 1
    beep()
    return local

def pair(x, y):
    x, y = y + 2, x + 3
    return x, y

def f(a, b):
    x = bump(a) + bump(b)
    a, b = b, a
    p, q = pair(bump(a), bump(b))
    z = bump(bump(a))
    return x, a, b, p, q, z
'''


BOOLEANS = '''
def mark(x):
    beep()
    return x

def f(a, b):
    x = mark(a) and mark(b)
    y = mark(a) or mark(b)
    z = not (mark(a) and (mark(b) or mark(3)))
    t = (a and b) + (a or b) + (not a)
    return x, y, z, t
'''


REPEATED = '''
def part(x):
    if x:
        local = x + 2
    return local

def f(a, b):
    x, y = part(a), part(0)
    i, total = 0, 0
    while True:
        if i >= b:
            break
        if i % 2:
            total += part(i)
        else:
            total += part(0)
        i += 1
    return x, y, total
'''


CONTROLLER = '''
def f(correct, all_wrong, budget):
    beep()
    j, i, tested = 0, 0, 0
    while tested < budget:
        mismatch = (all_wrong or j != correct) and i == j
        tested += 1
        if mismatch:
            beep()
            j += 1
            i = 0
        else:
            i += 1
    return j, i, tested
'''


def check_actual_controller(text, share=False):
    source = SourceVM(text, beep_limit=2)
    try:
        source.call('main', ())
    except AuditLimit as exc:
        assert exc.args[0] == ('beep limit reached', 2), exc
    else:
        raise AssertionError('controller returned')
    vm, _ = compile_and_run(text, 'main', (), share=share, beep_count=2)
    for snapshot, (_, registers) in zip(source.beeps, vm.beep_records):
        for key, value in snapshot.items():
            assert registers.get(key, 0) == value, (key, value, registers.get(key))
    assert [snapshot['main.j'] for snapshot in source.beeps] == [0, 0]
    return [step for step, _ in vm.beep_records]


def main():
    checks = 0
    maximum_steps = 0
    for share in (False, True):
        for a, b in product(range(8), repeat=2):
            steps, _ = check_fixture(ARITHMETIC, 'f', (a, b), share)
            maximum_steps = max(maximum_steps, steps)
            checks += 1
        for a, b in product(range(5), repeat=2):
            steps, _ = check_fixture('def f(a,b):\n    return a**b\n', 'f', (a, b), share)
            maximum_steps = max(maximum_steps, steps)
            checks += 1
        for source, domain in ((FLOW, range(6)), (CALLS, range(3)),
                               (BOOLEANS, range(4)), (REPEATED, range(5))):
            for args in product(domain, repeat=2):
                steps, _ = check_fixture(source, 'f', args, share)
                maximum_steps = max(maximum_steps, steps)
                checks += 1
        for args in ((37, 19), (100, 7), (1, 100), (1000, 1)):
            steps, _ = check_fixture(ARITHMETIC, 'f', args, share)
            maximum_steps = max(maximum_steps, steps)
            checks += 1
        for args in ((0, 0, 12), (3, 0, 20), (0, 1, 30)):
            steps, _ = check_fixture(CONTROLLER, 'f', args, share)
            maximum_steps = max(maximum_steps, steps)
            checks += 1
    production = (CODE / 'source.py').read_text()
    for share in (False, True):
        for code in range(1, 33):
            steps, _ = check_fixture(production, 'formula', (code,), share)
            maximum_steps = max(maximum_steps, steps)
            checks += 1
        for e in range(8):
            for f, w, t in ((1, 0, 0), (1, 0, 1), (4, 2, 1), (3, 1, 2)):
                steps, _ = check_fixture(production, 'run', (e, f, w, t), share)
                maximum_steps = max(maximum_steps, steps)
                checks += 1
    event_steps = {str(share): check_actual_controller(production, share)
                   for share in (False, True)}
    print(json.dumps({'status': 'pass', 'fixtures': checks,
                      'maximum_primitive_steps': maximum_steps,
                      'actual_controller_first_two_beeps': event_steps}, sort_keys=True))


if __name__ == '__main__':
    main()
