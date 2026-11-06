"""Direct natural affine accumulation over the inherited primitive grammar.

These are new optional compiler rules.  No source AST or frozen producer is
modified.  Multiplication is expanded only for small nonnegative constants;
all emitted operations remain the counted unary INC/DECNZ grammar.
"""
import ast

from half_pairs import HalfPairBuilder
from TMBuilder import subroutine


def pure_scalar(node):
    """Only total, effect-free expressions already in the source contract."""
    if isinstance(node, ast.Constant):
        return isinstance(node.value, (int, bool)) and node.value >= 0
    if isinstance(node, ast.Name):
        return isinstance(node.ctx, ast.Load)
    if isinstance(node, ast.BinOp) and isinstance(node.op,
            (ast.Add, ast.Sub, ast.Mult, ast.Pow, ast.FloorDiv, ast.Mod)):
        return pure_scalar(node.left) and pure_scalar(node.right)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return pure_scalar(node.operand)
    if isinstance(node, ast.BoolOp) and isinstance(node.op, (ast.And, ast.Or)):
        return all(pure_scalar(value) for value in node.values)
    if (isinstance(node, ast.Compare) and len(node.ops) == len(node.comparators) == 1
            and isinstance(node.ops[0], (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE))):
        return pure_scalar(node.left) and pure_scalar(node.comparators[0])
    return False


def linear_terms(node, scale=1):
    """Preserve left-to-right leaf order while flattening pure linear sums."""
    if not pure_scalar(node):
        return None
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left, right = linear_terms(node.left, scale), linear_terms(node.right, scale)
        return None if left is None or right is None else left+right
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        for constant, value in ((node.left, node.right), (node.right, node.left)):
            if (isinstance(constant, ast.Constant) and type(constant.value) is int
                    and 0 <= constant.value <= 8 and scale*constant.value <= 8):
                return linear_terms(value, scale*constant.value)
    return [(scale, node)]


class ArithmeticBuilder(HalfPairBuilder):
    def __init__(self, *args, affine_expressions=True, affine_updates=True,
                 affine_assignments=True, affine_forward=True, **kwargs):
        super().__init__(*args, **kwargs)
        self.affine_expressions = affine_expressions
        self.affine_updates = affine_updates
        self.affine_assignments = affine_assignments
        self.affine_forward = affine_forward
        self.arithmetic_certificate = []

    @subroutine
    def append_scaled(self, out, source, scale, consume):
        assert out != source and source != self.scratch and out != self.scratch
        assert type(scale) is int and 0 <= scale <= 8
        if scale == 1:
            return [self.move(out, source) if consume else self.copy(out, source)]
        if consume:
            return [self.while_decnz(source, [out.inc]*scale)]
        return [self.while_decnz(source, [out.inc]*scale+[self.scratch.inc]),
                self.move(source, self.scratch)]

    def append_terms(self, frame, out, terms):
        code = []
        for scale, node in terms:
            if scale == 0:
                continue
            if (isinstance(node, ast.Constant) and type(node.value) is int
                    and 0 <= node.value*scale <= 8):
                code += [out.inc]*(node.value*scale)
            elif isinstance(node, ast.Name):
                source = self.variable(frame, node.id)
                code += [self.append_scaled(out, source, scale,
                                           id(node) in self.live.consume)]
            else:
                part, value = self.expression(frame, node)
                forwarded = None
                nested = linear_terms(node)
                nested_affine = (self.affine_expressions and isinstance(node, ast.BinOp)
                    and nested is not None and not (len(nested) == 1 and nested[0] == (1, node)))
                if (self.affine_forward and part and not nested_affine
                        and isinstance(node, (ast.BinOp, ast.Compare))):
                    for result in self.micro:
                        last_move = self.memo.get(('move', value, result))
                        if last_move is not None and part[-1] == last_move:
                            assert forwarded is None
                            forwarded = result
                if forwarded is None:
                    code += part+[self.append_scaled(out, value, scale, True)]
                else:
                    # This inherited scalar arithmetic/comparison expression
                    # ends by moving its entire result into a still-zero owned
                    # output.  Exclude a recursively affine accumulator, whose
                    # last move might add only one term to an existing sum.
                    # Consume the shared result directly into this sum.
                    code += part[:-1]+[self.append_scaled(out, forwarded, scale, True)]
                    self.arithmetic_certificate.append(dict(function=frame['name'],
                        line=getattr(node, 'lineno', None), kind='affine-result-forward',
                        expression=ast.unparse(node), shared_result=str(forwarded),
                        discarded_owned_output=str(value), coefficient=scale))
                self.free(frame, value)
        return code

    def expression(self, frame, node):
        terms = linear_terms(node) if self.affine_expressions else None
        if (terms is None or (len(terms) == 1 and terms[0] == (1, node))
                or not isinstance(node, ast.BinOp)):
            return super().expression(frame, node)
        out = self.alloc(frame)
        code = self.append_terms(frame, out, terms)
        self.arithmetic_certificate.append(dict(function=frame['name'],
            line=getattr(node, 'lineno', None), kind='affine-expression',
            expression=ast.unparse(node), coefficients=[scale for scale, _ in terms]))
        return code, out

    def block(self, frame, statements, loops=()):
        code = []
        for node in statements:
            if (self.affine_updates and isinstance(node, ast.AugAssign)
                    and isinstance(node.target, ast.Name) and isinstance(node.op, ast.Add)
                    and not any(isinstance(value, ast.Name) and value.id == node.target.id
                                for value in ast.walk(node.value))):
                terms = linear_terms(node.value)
                # Complex terms can call arithmetic using the target as live
                # source state, but no new procedure call is admitted here.
                if terms is not None and not isinstance(node.value, ast.Constant):
                    target = self.variable(frame, node.target.id)
                    code += self.append_terms(frame, target, terms)
                    self.arithmetic_certificate.append(dict(function=frame['name'],
                        line=getattr(node, 'lineno', None), kind='affine-update',
                        target=node.target.id, expression=ast.unparse(node.value)))
                    continue
            if (self.affine_assignments and isinstance(node, ast.Assign)
                    and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)):
                target_name = node.targets[0].id
                terms = linear_terms(node.value)
                if (terms is not None and isinstance(node.value, ast.BinOp)
                        and not (len(terms) == 1 and terms[0] == (1, node.value))):
                    target = self.variable(frame, target_name)
                    occurrences = [value for value in ast.walk(node.value)
                                   if isinstance(value, ast.Name) and value.id == target_name]
                    target_atom = occurrences[0] if len(occurrences) == 1 else None
                    consume_target = any(atom is target_atom and scale > 0
                                         for scale, atom in terms)
                    captured, prepared = [], []
                    # Complex pure atoms are evaluated before the shared A
                    # accumulator becomes nonzero.  Duplicate source reads
                    # remain protected by the inherited whole-expression
                    # last-read exclusion, so reordering these captures cannot
                    # consume a value still needed by a later simple term.
                    for scale, atom in terms:
                        if scale == 0:
                            continue
                        if (isinstance(atom, ast.Name) or isinstance(atom, ast.Constant)
                                and type(atom.value) is int and 0 <= atom.value*scale <= 8):
                            prepared.append((scale, atom))
                        else:
                            part, value = self.expression(frame, atom)
                            code += part
                            captured.append(value)
                            prepared.append((scale, value))
                    A = self.micro[0]
                    for scale, atom in prepared:
                        if isinstance(atom, ast.Name):
                            source = self.variable(frame, atom.id)
                            consume = atom is target_atom and consume_target or id(atom) in self.live.consume
                            code += [self.append_scaled(A, source, scale, consume)]
                        elif isinstance(atom, ast.Constant):
                            code += [A.inc]*(atom.value*scale)
                        else:
                            code += [self.append_scaled(A, atom, scale, True)]
                    if not consume_target:
                        code += [self.clear(target)]
                    code += [self.move(target, A)]
                    for value in captured:
                        self.free(frame, value)
                    self.arithmetic_certificate.append(dict(function=frame['name'],
                        line=getattr(node, 'lineno', None), kind='affine-assignment',
                        target=target_name, expression=ast.unparse(node.value),
                        captured_atoms=len(captured), consumed_old_target=consume_target))
                    continue
            code += super().block(frame, [node], loops)
        return code
