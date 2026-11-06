"""Semantics-preserving small-constant lowerings for the natural compiler.

This module inherits the frozen compiler. It never evaluates a source function
at build time. Each rule expands to the same unbounded unary primitives and
retains natural arithmetic, source event order, and live source values.
"""
import ast
from natural import NaturalBuilder
from TMBuilder import subroutine


def small(node):
    return (int(node.value) if isinstance(node, ast.Constant)
            and isinstance(node.value, (int, bool)) and 0 <= node.value <= 4
            else None)


class OptimizedNaturalBuilder(NaturalBuilder):
    def __init__(self, *args, constants=True, inplace=True, consuming_returns=True,
                 fused_divmod=True, pooled_temporaries=False, **kwargs):
        super().__init__(*args, **kwargs)
        self.constants = constants
        self.inplace = inplace
        self.consuming_returns = consuming_returns
        self.fused_divmod = fused_divmod
        self.pooled_temporaries = pooled_temporaries
        self.heights = {}
        active = set()
        def height(name):
            if name in self.heights:
                return self.heights[name]
            if name in active:
                raise ValueError('recursive calls are unsupported')
            active.add(name)
            calls = [n.func.id for n in ast.walk(self.functions[name])
                     if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                     and n.func.id in self.functions]
            answer = max([height(callee) + 1 for callee in calls], default=0)
            active.remove(name)
            self.heights[name] = answer
            return answer
        height(self.entry)

    def alloc(self, frame):
        if not self.pooled_temporaries:
            return super().alloc(frame)
        index = 0
        while index in frame['used']:
            index += 1
        frame['used'].add(index)
        return self.reg(f"pool{self.heights[frame['name']]}.tmp{index}")

    def free(self, frame, register):
        if not self.pooled_temporaries:
            return super().free(frame, register)
        prefix = f"pool{self.heights[frame['name']]}.tmp"
        assert str(register).startswith(prefix)
        frame['used'].remove(int(str(register)[len(prefix):]))

    @subroutine
    def halve(self, q, r, a):
        # q=r=0. Each pair of consumed units increments q; final odd unit r=1.
        assert len({q, r, a}) == 3
        return [self.while_decnz(a, [r.inc,
            self.if_decnz(a, [self.clear(r), q.inc])])]

    def expression(self, frame, node):
        if self.constants and isinstance(node, ast.BinOp):
            if small(node.left) == 2 and isinstance(node.op, ast.Pow):
                code, exponent = self.expression(frame, node.right)
                out, work = self.alloc(frame), self.alloc(frame)
                code += [out.inc, self.while_decnz(exponent, [
                    self.while_decnz(out, [work.inc, work.inc]), self.move(out, work)])]
                self.free(frame, exponent)
                self.free(frame, work)
                return code, out
            c = small(node.right)
            if c is not None and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult)):
                code, a = self.expression(frame, node.left)
                if isinstance(node.op, ast.Add):
                    return code + [a.inc] * c, a
                if isinstance(node.op, ast.Sub):
                    return code + [self.dec(a)] * c, a
                if c == 0:
                    return code + [self.clear(a)], a
                if c == 1:
                    return code, a
                out = self.alloc(frame)
                code += [self.while_decnz(a, [out.inc] * c)]
                self.free(frame, a)
                return code, out
            c = small(node.left)
            if c is not None and isinstance(node.op, (ast.Add, ast.Mult)):
                # Moving a pure constant past the operand changes no effects.
                return self.expression(frame, ast.BinOp(left=node.right, op=node.op,
                                                       right=node.left))
            if small(node.right) == 2 and isinstance(node.op, (ast.FloorDiv, ast.Mod)):
                code, a = self.expression(frame, node.left)
                q, r = self.alloc(frame), self.alloc(frame)
                code += [self.halve(q, r, a)]
                self.free(frame, a)
                out, dead = (q, r) if isinstance(node.op, ast.FloorDiv) else (r, q)
                code += [self.clear(dead)]
                self.free(frame, dead)
                return code, out
            if small(node.right) == 4 and isinstance(node.op, ast.FloorDiv):
                code, a = self.expression(frame, node.left)
                q, r, out = self.alloc(frame), self.alloc(frame), self.alloc(frame)
                code += [self.halve(q, r, a), self.clear(r),
                         self.halve(out, r, q), self.clear(r)]
                for dead in (a, q, r):
                    self.free(frame, dead)
                return code, out
        if (self.constants and isinstance(node, ast.Compare) and len(node.ops) == 1
                and small(node.comparators[0]) is not None):
            c = small(node.comparators[0])
            op = node.ops[0]
            code, a = self.expression(frame, node.left)
            out = self.alloc(frame)
            if isinstance(op, (ast.Eq, ast.NotEq)):
                body = [self.if_zero(a, out.inc)]
                for _ in range(c):
                    body = [self.if_decnz(a, body)]
                code += body + [self.clear(a)]
                if isinstance(op, ast.NotEq):
                    inv = self.alloc(frame)
                    code += [self.if_zero(out, inv.inc), self.clear(out)]
                    self.free(frame, out)
                    out = inv
            elif isinstance(op, (ast.Gt, ast.GtE, ast.Lt, ast.LtE)):
                # >c and <=c inspect max(a-c,0); >=c and <c use c-1.
                if c == 0 and isinstance(op, (ast.GtE, ast.Lt)):
                    code += [self.clear(a)]
                    if isinstance(op, ast.GtE):
                        code += [out.inc]
                else:
                    decrements = c if isinstance(op, (ast.Gt, ast.LtE)) else c - 1
                    code += [self.dec(a)] * decrements
                    if isinstance(op, (ast.Gt, ast.GtE)):
                        code += [self.truth(out, a)]
                    else:
                        code += [self.if_zero(a, out.inc), self.clear(a)]
            else:
                raise ValueError('unsupported comparison')
            self.free(frame, a)
            return code, out
        return super().expression(frame, node)

    def block(self, frame, statements, loops=()):
        code = []
        for node in statements:
            if (self.fused_divmod and isinstance(node, ast.Assign)
                    and len(node.targets) == 1 and isinstance(node.targets[0], ast.Tuple)
                    and len(node.targets[0].elts) == 2 and isinstance(node.value, ast.Tuple)
                    and len(node.value.elts) == 2):
                targets, values = node.targets[0].elts, node.value.elts
                rvalue, qvalue = values
                if (all(isinstance(x, ast.Name) for x in targets)
                        and isinstance(rvalue, ast.BinOp) and isinstance(rvalue.op, ast.Mod)
                        and isinstance(qvalue, ast.BinOp) and isinstance(qvalue.op, ast.FloorDiv)
                        and isinstance(rvalue.left, ast.Name) and isinstance(qvalue.left, ast.Name)
                        and rvalue.left.id == qvalue.left.id == targets[1].id
                        and targets[0].id != targets[1].id
                        and small(rvalue.right) == small(qvalue.right) == 2):
                    a, result = self.variable(frame, targets[1].id), self.variable(frame, targets[0].id)
                    q, r = self.alloc(frame), self.alloc(frame)
                    code += [self.halve(q, r, a), self.clear(result),
                             self.move(result, r), self.move(a, q)]
                    self.free(frame, q)
                    self.free(frame, r)
                    continue
            if (self.inplace and isinstance(node, ast.AugAssign)
                    and isinstance(node.target, ast.Name) and small(node.value) is not None):
                a, c = self.variable(frame, node.target.id), small(node.value)
                if isinstance(node.op, ast.Add):
                    code += [a.inc] * c
                    continue
                if isinstance(node.op, ast.Sub):
                    code += [self.dec(a)] * c
                    continue
                if c == 2 and isinstance(node.op, (ast.FloorDiv, ast.Mod)):
                    q, r = self.alloc(frame), self.alloc(frame)
                    code += [self.halve(q, r, a)]
                    out, dead = (q, r) if isinstance(node.op, ast.FloorDiv) else (r, q)
                    code += [self.move(a, out), self.clear(dead)]
                    self.free(frame, q)
                    self.free(frame, r)
                    continue
                if isinstance(node.op, ast.Mult):
                    if c == 0:
                        code += [self.clear(a)]
                    elif c != 1:
                        out = self.alloc(frame)
                        code += [self.while_decnz(a, [out.inc] * c), self.move(a, out)]
                        self.free(frame, out)
                    continue
            code += super().block(frame, [node], loops)
        return code

    def call(self, frame, node):
        if not self.consuming_returns:
            return super().call(frame, node)
        if not isinstance(node.func, ast.Name) or node.keywords or node.func.id == 'main':
            raise ValueError('only positional nonrecursive procedure calls are accepted')
        name = node.func.id
        body, callee = self.compile_function(name)
        if len(node.args) != len(callee['args']):
            raise ValueError('argument count mismatch')
        code, args = [], []
        for argument in node.args:
            more, value = self.expression(frame, argument)
            code += more
            args.append(value)
        for name_, value in zip(callee['args'], args):
            target = self.variable(callee, name_)
            code += [self.clear(target), self.move(target, value)]
            self.free(frame, value)
        code += [body]
        outputs = []
        for result in callee['returns']:
            out = self.alloc(frame)
            code += [self.move(out, result)]
            outputs.append(out)
        return code, outputs
