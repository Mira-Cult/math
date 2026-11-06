"""Audited definite-assignment omission of dead procedure-entry resets.

Separate candidate extension: optimized_natural.py remains frozen unchanged.
"""
import ast
from optimized_natural import OptimizedNaturalBuilder


def assignment_certificate(function):
    """Conservative all-path first-read audit; no bounded execution involved.

    Return read-before-assignment variables and possible normal fallthrough.
    Loops never export newly assigned variables. This deliberately misses some
    savings rather than assume a loop executes or terminates.
    """
    missing = set()

    def expr(node, assigned):
        if isinstance(node, ast.Name):
            if node.id not in assigned:
                missing.add(node.id)
        elif isinstance(node, ast.Call):
            for argument in node.args:
                expr(argument, assigned)
        else:
            for child in ast.iter_child_nodes(node):
                expr(child, assigned)

    def block(statements, initial):
        assigned = set(initial)
        for node in statements:
            if isinstance(node, ast.Assign):
                expr(node.value, assigned)
                targets = node.targets[0].elts if isinstance(node.targets[0], ast.Tuple) else node.targets
                assigned.update(target.id for target in targets)
            elif isinstance(node, ast.AugAssign):
                expr(node.target, assigned)
                expr(node.value, assigned)
                assigned.add(node.target.id)
            elif isinstance(node, ast.If):
                expr(node.test, assigned)
                yes = block(node.body, assigned)
                no = block(node.orelse, assigned)
                if yes is None and no is None:
                    return None
                assigned = no if yes is None else yes if no is None else yes & no
            elif isinstance(node, ast.While):
                expr(node.test, assigned)
                block(node.body, assigned)
                # Even a constant-true loop is conservatively allowed to exit;
                # this cannot incorrectly erase a required initialization.
            elif isinstance(node, ast.Return):
                expr(node.value, assigned)
                return None
            elif isinstance(node, (ast.Break, ast.Continue)):
                return None
            elif isinstance(node, ast.Expr):
                expr(node.value, assigned)
            else:
                raise ValueError('unsupported definite-assignment statement')
        return assigned

    initial = {a.arg for a in function.args.args}
    normal = block(function.body, initial)
    return dict(read_before_assignment=sorted(missing), may_fallthrough=normal is not None)


class AssignedNaturalBuilder(OptimizedNaturalBuilder):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.assignment_certificates = {}

    def compile_function(self, name):
        if name in self.compiled:
            return self.compiled[name], self.frames[name]
        body, frame = super().compile_function(name)
        certificate = assignment_certificate(self.functions[name])
        self.assignment_certificates[name] = certificate
        parameters = {str(self.variable(frame, a)) for a in frame['args']}
        locals_ = [r for r in self.registers.values() if r.startswith(name + '.')
                   and str(r) not in parameters]
        assert len(body) == len(locals_) + 1
        retained = []
        omitted = []
        returns = set(frame['returns'])
        for register, initializer in zip(locals_, body[:-1]):
            assert initializer == self.clear(register)
            localname = str(register)[len(name) + 1:]
            needed = (certificate['may_fallthrough'] if register in returns else
                      localname in certificate['read_before_assignment'])
            if needed:
                retained.append(initializer)
            else:
                omitted.append(str(register))
        result = retained + [body[-1]]
        certificate['omitted_entry_resets'] = omitted
        certificate['retained_entry_resets'] = [str(r) for r in locals_ if str(r) not in omitted]
        self.compiled[name] = result
        return result, frame
