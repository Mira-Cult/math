"""Closed exact normalized clock assignment, borrowing and restoring its exponent.

Transferred contract: P=NP direct_clock/PROOF.md at donor 9834b2b,
with base N+1 rather than N+2.  The actual compiler is the NP backend.
"""
import ast
from contextlib import contextmanager
from itertools import combinations
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
COMPACT = HERE.parents[1]
sys.path.insert(0, str(COMPACT/'binary_phase/control/parser'))
import build_parser
from build_parser import lower_half, build_coalesced
import live_registers


def match(node):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and isinstance(node.value, ast.BinOp)
            and isinstance(node.value.op, ast.Pow)
            and isinstance(node.value.right, ast.Name)
            and isinstance(node.value.left, ast.BinOp)
            and isinstance(node.value.left.op, ast.Add)
            and isinstance(node.value.left.left, ast.Name)
            and isinstance(node.value.left.right, ast.Constant)
            and type(node.value.left.right.value) is int
            and node.value.left.right.value == 1):
        return None
    names = (node.targets[0].id, node.value.left.left.id, node.value.right.id)
    return names if len(set(names)) == 3 else None


@contextmanager
def installed(*, borrow=True):
    original_block = lower_half.NativeHalfMixin.block
    original_interference = live_registers.interference

    def interference(function, registers, returns, retained_resets, reuse_returns):
        cfg, graph = original_interference(function, registers, returns, retained_resets, reuse_returns)
        obligations = []
        for statement in ast.walk(function):
            names = match(statement)
            if names is None:
                continue
            for left, right in combinations(names, 2):
                assert left in graph and right in graph
                graph[left].add(right)
                graph[right].add(left)
            obligations.append(dict(line=statement.lineno, operands=list(names),
                reason='closed clock resets output before its last master read; three simultaneous source operands'))
        if obligations:
            cfg['closed_clock_interference'] = obligations
        return cfg, graph

    def block(self, frame, statements, loops=()):
        code, pending = [], []
        if not hasattr(self, 'direct_clock_certificate'):
            self.direct_clock_certificate = []
        for statement in statements:
            names = match(statement)
            if names is None:
                pending.append(statement)
                continue
            if pending:
                code += original_block(self, frame, pending, loops)
                pending = []
            F, N, K = [self.variable(frame, name) for name in names]
            B, Q, C = self.micro[1], self.micro[2], self.scratch
            assert len({F, N, K, B, Q, C}) == 6
            product = [self.while_decnz(F, [self.copy(Q, N), Q.inc]), self.move(F, Q)]
            if borrow:
                region = [self.clear(F), F.inc,
                    self.while_decnz(K, [B.inc, product]), self.move(K, B)]
            else:
                region = [self.clear(F), F.inc, self.copy(B, K),
                    self.while_decnz(B, product)]
            code += region
            self.direct_clock_certificate.append(dict(
                function=frame['name'], line=statement.lineno,
                exact_ast=ast.dump(statement, include_attributes=False),
                output=str(F), length_master=str(N), exponent_master=str(K),
                exponent_work=str(B), product_work=str(Q), copy_scratch=str(C),
                borrow_exponent=borrow,
                entry='six distinct logical operands; arbitrary natural F,N,K; B=Q=C=0',
                invariant=('after t iterations F=(N+1)^t, K=old_K-t, B=t, Q=C=0' if borrow
                    else 'after t iterations F=(N+1)^t, B=old_K-t, K=old_K, Q=C=0'),
                exit='F=(old_N+1)^old_K; N,K restored; B=Q=C=0; other logical cells preserved',
                progress='finite stale-output reset, finite outer countdown, finite inner countdown, preserving copies and restoration',
                source_allocation='explicit three-operand interference before frame pooling',
                source_scope='same normalized clock on all naturals, including N=0 and K=0; no new physical primitive'))
        if pending:
            code += original_block(self, frame, pending, loops)
        return code

    lower_half.NativeHalfMixin.block = block
    live_registers.interference = interference
    try:
        yield
    finally:
        lower_half.NativeHalfMixin.block = original_block
        live_registers.interference = original_interference
