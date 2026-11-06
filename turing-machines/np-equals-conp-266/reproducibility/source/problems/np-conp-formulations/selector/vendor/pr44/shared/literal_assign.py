"""Direct lowering of literal assignments and literal returns.

This is a separate extension; all previous optimization modules stay frozen.
"""
import ast
from frame_pool import FramePooledBuilder
from optimized_natural import small


class LiteralAssignBuilder(FramePooledBuilder):
    def block(self, frame, statements, loops=()):
        code=[]
        for node in statements:
            if isinstance(node,ast.Assign) and len(node.targets)==1:
                target=node.targets[0]
                targets=target.elts if isinstance(target,ast.Tuple) else [target]
                values=node.value.elts if isinstance(node.value,ast.Tuple) else [node.value]
                if (len(targets)==len(values) and all(isinstance(t,ast.Name) for t in targets)
                        and all(small(v) is not None for v in values)):
                    for target,value in zip(targets,values):
                        register=self.variable(frame,target.id)
                        code += [self.clear(register)] + [register.inc]*small(value)
                    continue
            if isinstance(node,ast.Return):
                values=node.value.elts if isinstance(node.value,ast.Tuple) else [node.value]
                if (len(values)==len(frame['returns'])
                        and all(small(v) is not None for v in values)):
                    for register,value in zip(frame['returns'],values):
                        code += [self.clear(register)] + [register.inc]*small(value)
                    code += ['break_'+frame['label']]
                    continue
            code += super().block(frame,[node],loops)
        return code
