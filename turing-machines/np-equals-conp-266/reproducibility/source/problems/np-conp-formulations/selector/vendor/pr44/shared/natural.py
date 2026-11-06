"""A complete natural-number AST -> unary-register -> binary TM compiler.

Accepted source: nonrecursive, fixed-arity procedures; natural constants/names;
simultaneous assignments; +=, -=, *=, //=, %=; +, saturating -, *, //, %, **;
comparisons; short-circuit and/or/not; if, while, break, continue, return; beep().
Division by zero is defined as quotient 0, remainder dividend.  Registers have
no fixed width.  Compilation terminates on the finite, acyclic call graph.

Only the source file is parsed, never evaluated by this compiler.  Every macro
below expands to the two unary primitives INC and DECNZ and lexical control.
The vendored backend emits actual single-tape binary transitions.
"""
from __future__ import annotations

import ast
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / 'vendor'))
from TMBuilder import TMBuilder, subroutine
import tm


class NaturalBuilder(TMBuilder):
    def __init__(self, source, entry='main', entry_args=(), *, share=False):
        super().__init__()
        self.source = str(source)
        module = ast.parse(self.source)
        self.functions = {}
        for node in module.body:
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                continue
            if not isinstance(node, ast.FunctionDef) or node.name in self.functions:
                raise ValueError('only distinct procedure definitions are accepted')
            if node.decorator_list or node.args.defaults or node.args.kwonlyargs or node.args.vararg or node.args.kwarg or node.args.posonlyargs:
                raise ValueError('only fixed positional arguments are accepted')
            self.functions[node.name] = node
        self.entry = entry
        self.entry_args = tuple(entry_args)
        if any(type(number) is not int or number < 0 for number in self.entry_args):
            raise ValueError('entry arguments must be natural integers')
        self.share = share
        self.compiled = {}
        self.compiling = set()
        self.frames = {}
        self.uid = 0
        self.scratch = self.reg('scratch.copy')
        self.stats = {}

    def fresh(self, prefix):
        self.uid += 1
        return prefix + str(self.uid)

    @subroutine
    def clear(self, x):
        return [self.while_decnz(x, ())]

    @subroutine
    def move(self, out, x):
        assert out != x
        return [self.while_decnz(x, out.inc)]

    @subroutine
    def copy(self, out, x):
        assert len({out, x, self.scratch}) == 3
        return [self.while_decnz(x, [out.inc, self.scratch.inc]),
                self.move(x, self.scratch)]

    @subroutine
    def dec(self, x):
        # The explicit lexical exit keeps the test's enclosing pair present.
        # An empty second branch would be flattened by the backend and be wrong.
        return [self.label('dec', [x.decnz, 'break_dec'])]

    @subroutine
    def if_nz(self, x, body):
        if body == ():
            return []
        return [self.if_decnz(x, [x.inc, body])]

    @subroutine
    def if_zero(self, x, body):
        if body == ():
            return []
        return [self.label('zero', [[x.decnz, [x.inc, 'break_zero']], body])]

    @subroutine
    def truth(self, out, x):
        # out is zero; consume x and replace its truth value in out.
        return [self.if_decnz(x, [out.inc, self.clear(x)])]

    @subroutine
    def subtract(self, a, b):
        # a <- max(a-b,0), b <- 0.
        return [self.while_decnz(b, self.dec(a))]

    @subroutine
    def multiply(self, out, a, b):
        # out is zero; consume a,b, preserving the shared copy scratch as zero.
        return [self.while_decnz(b, self.copy(out, a)), self.clear(a)]

    @subroutine
    def power(self, out, a, b, work):
        # All four registers distinct; out=work=0; a,b consumed.
        return [out.inc, self.while_decnz(b, [
            self.while_decnz(out, self.copy(work, a)), self.move(out, work)]),
            self.clear(a)]

    @subroutine
    def divmod(self, q, r, a, b, countdown):
        # q=r=countdown=0. Consume a,b. For b=0, (q,r)=(0,a).
        return [self.if_nz(b, [self.copy(countdown, b),
            self.while_decnz(a, [r.inc, self.dec(countdown),
                self.if_zero(countdown, [q.inc, self.clear(r), self.copy(countdown, b)])])]),
            self.move(r, a), self.clear(b), self.clear(countdown)]

    @subroutine
    def equal(self, out, a, b):
        # Consume a,b; out=0 becomes [a=b].
        return [self.label('eq', [
            self.while_decnz(a, [self.if_zero(b, [self.clear(a), 'break_eq']), self.dec(b)]),
            self.if_zero(b, out.inc)]), self.clear(b)]

    def alloc(self, frame):
        used = frame['used']
        index = 0
        while index in used:
            index += 1
        used.add(index)
        return self.reg(frame['name'] + '.tmp' + str(index))

    def free(self, frame, register):
        prefix = frame['name'] + '.tmp'
        assert str(register).startswith(prefix)
        frame['used'].remove(int(str(register)[len(prefix):]))

    def variable(self, frame, name):
        if name.startswith('tmp') or name.startswith('ret'):
            raise ValueError('reserved local name')
        return self.reg(frame['name'] + '.' + name)

    def normalize(self, frame, code, value):
        result = self.alloc(frame)
        code += [self.truth(result, value)]
        self.free(frame, value)
        return code, result

    def expression(self, frame, node):
        if isinstance(node, ast.Constant):
            if not isinstance(node.value, (int, bool)) or node.value < 0:
                raise ValueError('expected natural constant')
            out = self.alloc(frame)
            return [out.inc] * int(node.value), out
        if isinstance(node, ast.Name):
            out = self.alloc(frame)
            return [self.copy(out, self.variable(frame, node.id))], out
        if isinstance(node, ast.Call):
            code, outputs = self.call(frame, node)
            if len(outputs) != 1:
                raise ValueError('a scalar expression needs one return value')
            return code, outputs[0]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            code, value = self.expression(frame, node.operand)
            out = self.alloc(frame)
            code += [self.if_zero(value, out.inc), self.clear(value)]
            self.free(frame, value)
            return code, out
        if isinstance(node, ast.BoolOp):
            code, out = self.expression(frame, node.values[0])
            code, out = self.normalize(frame, code, out)
            for operand in node.values[1:]:
                rhs, val = self.expression(frame, operand)
                rhs, val = self.normalize(frame, rhs, val)
                rhs = [self.clear(out), rhs, self.move(out, val)]
                code += [self.if_nz(out, rhs) if isinstance(node.op, ast.And) else self.if_zero(out, rhs)]
                self.free(frame, val)
            return code, out
        if isinstance(node, ast.BinOp):
            code, a = self.expression(frame, node.left)
            right, b = self.expression(frame, node.right)
            code += right
            if isinstance(node.op, ast.Add):
                code += [self.move(a, b)]
                self.free(frame, b)
                return code, a
            if isinstance(node.op, ast.Sub):
                code += [self.subtract(a, b)]
                self.free(frame, b)
                return code, a
            out = self.alloc(frame)
            if isinstance(node.op, ast.Mult):
                code += [self.multiply(out, a, b)]
            elif isinstance(node.op, ast.Pow):
                work = self.alloc(frame)
                code += [self.power(out, a, b, work)]
                self.free(frame, work)
            elif isinstance(node.op, (ast.FloorDiv, ast.Mod)):
                remainder, countdown = self.alloc(frame), self.alloc(frame)
                code += [self.divmod(out, remainder, a, b, countdown)]
                self.free(frame, countdown)
                if isinstance(node.op, ast.Mod):
                    code += [self.clear(out)]
                    self.free(frame, out)
                    out = remainder
                else:
                    code += [self.clear(remainder)]
                    self.free(frame, remainder)
            else:
                raise ValueError('unsupported binary operator')
            self.free(frame, a)
            self.free(frame, b)
            return code, out
        if isinstance(node, ast.Compare):
            if len(node.ops) != 1:
                raise ValueError('chained comparisons are not accepted')
            code, a = self.expression(frame, node.left)
            more, b = self.expression(frame, node.comparators[0])
            code += more
            out = self.alloc(frame)
            op = node.ops[0]
            if isinstance(op, (ast.Eq, ast.NotEq)):
                code += [self.equal(out, a, b)]
                if isinstance(op, ast.NotEq):
                    neg = self.alloc(frame)
                    code += [self.if_zero(out, neg.inc), self.clear(out)]
                    self.free(frame, out)
                    out = neg
            elif isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                if isinstance(op, (ast.Gt, ast.GtE)):
                    a, b = b, a
                # Now test a<b or a<=b via b-a, adding one to b for <=.
                if isinstance(op, (ast.LtE, ast.GtE)):
                    code += [b.inc]
                code += [self.subtract(b, a), self.truth(out, b)]
            else:
                raise ValueError('unsupported comparison')
            self.free(frame, a)
            self.free(frame, b)
            return code, out
        raise ValueError('unsupported expression: ' + ast.dump(node))

    def call(self, frame, node):
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
            code += [self.copy(out, result)]
            outputs.append(out)
        return code, outputs

    def values(self, frame, node):
        if isinstance(node, ast.Call):
            return self.call(frame, node)
        nodes = node.elts if isinstance(node, (ast.Tuple, ast.List)) else [node]
        code, values = [], []
        for child in nodes:
            part, value = self.expression(frame, child)
            code += part
            values.append(value)
        return code, values

    def block(self, frame, statements, loops=()):
        code = []
        for node in statements:
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                continue
            if isinstance(node, ast.Assign):
                if len(node.targets) != 1:
                    raise ValueError('chained assignment is unsupported')
                target = node.targets[0]
                targets = target.elts if isinstance(target, ast.Tuple) else [target]
                part, values = self.values(frame, node.value)
                if len(targets) != len(values) or not all(isinstance(x, ast.Name) for x in targets):
                    raise ValueError('assignment arity or target mismatch')
                code += part
                for target_, value in zip(targets, values):
                    out = self.variable(frame, target_.id)
                    code += [self.clear(out), self.move(out, value)]
                    self.free(frame, value)
            elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                synthetic = ast.Assign(targets=[node.target], value=ast.BinOp(left=ast.Name(id=node.target.id, ctx=ast.Load()), op=node.op, right=node.value))
                code += self.block(frame, [synthetic], loops)
            elif isinstance(node, ast.If):
                part, condition = self.expression(frame, node.test)
                part, condition = self.normalize(frame, part, condition)
                label = self.fresh('if')
                yes = self.block(frame, node.body, loops)
                no = self.block(frame, node.orelse, loops)
                code += part + [self.label(label, [[condition.decnz, [yes, 'break_' + label]], no])]
                self.free(frame, condition)
            elif isinstance(node, ast.While):
                if node.orelse:
                    raise ValueError('while else is unsupported')
                label = self.fresh('loop')
                if isinstance(node.test, ast.Constant) and node.test.value is True:
                    body = self.block(frame, node.body, loops + (label,))
                    code += [self.label(label, [body, 'continue_' + label])]
                else:
                    part, condition = self.expression(frame, node.test)
                    part, condition = self.normalize(frame, part, condition)
                    body = self.block(frame, node.body, loops + (label,))
                    code += [self.label(label, [part, [condition.decnz, [body, 'continue_' + label]]])]
                    self.free(frame, condition)
            elif isinstance(node, (ast.Break, ast.Continue)):
                if not loops:
                    raise ValueError('loop control outside loop')
                code += [('break_' if isinstance(node, ast.Break) else 'continue_') + loops[-1]]
            elif isinstance(node, ast.Return):
                part, values = self.values(frame, node.value)
                if len(values) != len(frame['returns']):
                    raise ValueError('return arity mismatch')
                code += part
                for target, value in zip(frame['returns'], values):
                    code += [self.clear(target), self.move(target, value)]
                    self.free(frame, value)
                code += ['break_' + frame['label']]
            elif (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
                  and isinstance(node.value.func, ast.Name) and node.value.func.id == 'beep'
                  and not node.value.args and not node.value.keywords):
                code += ['beep']
            else:
                raise ValueError('unsupported statement: ' + ast.dump(node))
        return code

    def compile_function(self, name):
        if name in self.compiled:
            return self.compiled[name], self.frames[name]
        if name in self.compiling:
            raise ValueError('recursive calls are unsupported')
        if name not in self.functions:
            raise ValueError('unknown procedure ' + name)
        self.compiling.add(name)
        function = self.functions[name]
        arities = {len(n.value.elts) if isinstance(n.value, ast.Tuple) else 1
                   for n in ast.walk(function) if isinstance(n, ast.Return)}
        if len(arities) > 1:
            raise ValueError('inconsistent return arities')
        arity = next(iter(arities), 0)
        frame = {'name': name, 'args': [a.arg for a in function.args.args],
                 'label': self.fresh('fn'), 'used': set(),
                 'returns': [self.reg(name + '.ret' + str(i)) for i in range(arity)]}
        self.frames[name] = frame
        for arg in frame['args']:
            self.variable(frame, arg)
        body = self.block(frame, function.body)
        assert not frame['used'], (name, frame['used'])
        # Each call has fresh zero-initialized locals (parameter values retained).
        locals_ = [r for r in self.registers.values() if r.startswith(name + '.')
                   and r not in [self.variable(frame, a) for a in frame['args']]]
        result = [self.clear(r) for r in locals_] + [self.label(frame['label'], body)]
        self.compiled[name] = result
        self.compiling.remove(name)
        return result, frame

    @subroutine
    def main(self):
        body, frame = self.compile_function(self.entry)
        if len(self.entry_args) != len(frame['args']):
            raise ValueError('entry argument count mismatch')
        if self.entry == 'main' and not self.entry_args:
            return body
        init = []
        for name, number in zip(frame['args'], self.entry_args):
            r = self.variable(frame, name)
            init += [self.clear(r)] + [r.inc] * number
        # Fixtures end by beeping then repeat; the research source never returns.
        return init + [body, 'beep']

    def build_tree(self):
        self.main()
        if self.share:
            self.breakout_common_subsequences()
        self.reduce_to_cons()
        self.name_sequences()
        unresolved = set().union(*(s.unresolved_labels for s in self.sequences))
        # Dead nodes may still carry unresolved lexical labels; only live nodes matter.
        live = list(self.reachable())
        for i in live:
            assert not self.sequences[i].unresolved_labels, self.sequences[i].unresolved_labels
        return self

    def build_machine(self):
        self.build_tree()
        self.generate()
        # A beep is a successful primitive with no register change.  B executes
        # exactly one ordinary break transition and is never its own successor.
        self.tm.states['beep', '0'] = tm.Transition('1', 'R', '1b.reg.prep_1')
        self.tm.states['beep', '1'] = tm.Transition('0', 'L', 'B')
        self.tm.states['B', '0'] = tm.Transition('1', 'R', '2e.reg.cleanup_1')
        self.tm.states['B', '1'] = tm.Transition('0', 'L', '6.break.0')
        self.tm.gc()
        self.tm.statename = self.tm.start
        return self
