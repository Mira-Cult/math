"""Optional multiplication/addition fusion for a destructive Horner assignment.

Only three distinct named operands are accepted, and the overwritten target
must be one of the multiplication inputs.  This keeps argument liveness local.
"""
import ast
from kernel_builder import KernelBuilder,GenericKernelBuilder


class HornerMixin:
    def __init__(self,*args,horner_fusion=True,horner_reverse=True,**kwargs):
        super().__init__(*args,**kwargs)
        self.horner_fusion=horner_fusion
        self.horner_reverse=horner_reverse
        self.horner_certificate=[]

    def block(self,frame,statements,loops=()):
        if not self.horner_fusion:return super().block(frame,statements,loops)
        code=[]
        for node in statements:
            match=False
            if (isinstance(node,ast.Assign) and len(node.targets)==1 and
                isinstance(node.targets[0],ast.Name) and isinstance(node.value,ast.BinOp)
                and isinstance(node.value.op,ast.Add) and isinstance(node.value.left,ast.BinOp)
                and isinstance(node.value.left.op,ast.Mult)):
                x,y,z=node.value.left.left,node.value.left.right,node.value.right
                target=node.targets[0]
                match=(all(isinstance(v,ast.Name) for v in (x,y,z))
                    and len({x.id,y.id,z.id})==3 and target.id in (x.id,y.id))
            if not match:
                code+=super().block(frame,[node],loops);continue
            operands=[]
            for operand in (x,y,z):
                part,value=self.operand(frame,operand)
                assert not part and value[0] in ('reference','consume')
                if operand.id==target.id:value=('consume',value[1])
                operands.append(value)
            A,B,Q,R,C=self.micro
            multipliers=operands[:2]
            if self.horner_reverse:multipliers.reverse()
            code+=self.load_operand(A,multipliers[0])+self.load_operand(B,multipliers[1])
            code+=[self.product_kernel()]
            # Named-reference copy and move add to a possibly nonzero output.
            # Constant loading is intentionally excluded from this rule.
            code+=self.load_operand(Q,operands[2])
            destination=self.variable(frame,target.id)
            code+=[self.move(destination,Q)]
            self.horner_certificate.append(dict(function=frame['name'],
                line=getattr(node,'lineno',None),target=target.id,
                operands=[v.id for v in (x,y,z)],
                operand_modes=[v[0] for v in operands],
                reversed_multipliers=self.horner_reverse))
        return code


class HornerBuilder(HornerMixin,KernelBuilder):
    pass


class GenericHornerBuilder(HornerMixin,GenericKernelBuilder):
    pass
