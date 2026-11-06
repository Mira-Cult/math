from digits import DigitBuilder
from TMBuilder import subroutine
import ast
class IntrinsicBuilder(DigitBuilder):
    def __init__(self,*a,small_ops=True,small_compare=True,small_power=True,small_half=True,var_guards=True,**kw):
        super().__init__(*a,**kw)
        self.small_ops=small_ops;self.small_compare=small_compare;self.small_power=small_power;self.small_half=small_half;self.var_guards=var_guards
        self.intrinsic_certificate=[]
    def constant_kernel(self,op,c):
        a,b,q,r,z=self.micro
        if op=='Add':return [a.inc]*c
        if op=='Sub':return [self.dec(a)]*c
        if op=='Mult':return [self.while_decnz(a,[q.inc]*c)] if c else [self.clear(a)]
        if op=='PowBase':return [q.inc,self.while_decnz(a,[self.while_decnz(q,[r.inc]*c),self.move(q,r)])]
        if op in ('Eq','NotEq'):
            body=[self.if_zero(a,q.inc)]
            for _ in range(c):body=[self.if_decnz(a,body)]
            ans=body+[self.clear(a)]
            if op=='NotEq':ans += [self.if_zero(q,a.inc),self.clear(q),self.move(q,a)]
            return ans
        if op in ('Gt','GtE','Lt','LtE'):
            if c==0 and op in ('GtE','Lt'):return [self.clear(a)]+([q.inc] if op=='GtE' else [])
            n=c if op in ('Gt','LtE') else c-1
            ans=[self.dec(a)]*n
            if op in ('Gt','GtE'):ans += [self.truth(q,a)]
            else:ans += [self.if_zero(a,q.inc),self.clear(a)]
            return ans
        if op in ('Half','Parity'):return [self.half_kernel(),self.clear(r if op=='Half' else q)]
        raise ValueError(op)
    def small_pattern(self,node):
        if isinstance(node,ast.BinOp):left,right,op=node.left,node.right,type(node.op).__name__
        elif isinstance(node,ast.Compare) and len(node.ops)==1:left,right,op=node.left,node.comparators[0],type(node.ops[0]).__name__
        else:return None
        def small(x):return int(x.value) if isinstance(x,ast.Constant) and isinstance(x.value,(int,bool)) and 0<=x.value<=8 else None
        c=small(right)
        if self.small_power and op=='Pow' and small(left) in (2,3):return right,'PowBase',small(left),'q'
        if self.small_ops and op in ('Mult','Add') and small(left) is not None:left,right=right,left;c=small(right)
        if self.small_ops and c is not None and op in ('Add','Sub','Mult'):return left,op,c,'q' if op=='Mult' else 'a'
        if self.small_compare and c is not None and op in ('Eq','NotEq','Lt','Gt','LtE','GtE'):return left,op,c,'q'
        if self.small_half and c==2 and op in ('FloorDiv','Mod'):return left,'Half' if op=='FloorDiv' else 'Parity',2,'q' if op=='FloorDiv' else 'r'
        return None
    def expression(self,frame,node):
        p=self.small_pattern(node)
        if p is None:return super().expression(frame,node)
        operand,op,c,result=p
        code,value=self.operand(frame,operand);code+=self.load_operand(self.micro[0],value)
        if value[0]=='owned':self.free(frame,value[1])
        code += [self.constant_kernel(op,c)]
        out=self.alloc(frame);result=dict(zip('abqrc',self.micro))[result];code += [self.move(out,result)]
        self.intrinsic_certificate.append({'line':getattr(node,'lineno',None),'op':op,'constant':c})
        return code,out
    def direct_condition(self,frame,node):
        p=self.small_pattern(node)
        if p is not None and isinstance(node,ast.Compare):
            operand,op,c,result=p
            code,value=self.operand(frame,operand);code+=self.load_operand(self.micro[0],value)
            if value[0]=='owned':self.free(frame,value[1])
            code += [self.constant_kernel(op,c)]
            return code,self.micro[2]
        return super().direct_condition(frame,node)
    def block(self,frame,statements,loops=()):
        ans=[]
        for node in statements:
            test=node.test if isinstance(node,(ast.If,ast.While)) else None
            inv=False;base=test
            if isinstance(base,ast.UnaryOp) and isinstance(base.op,ast.Not):inv=True;base=base.operand
            if isinstance(base,ast.Compare) and len(base.ops)==1 and isinstance(base.ops[0],(ast.Eq,ast.NotEq)) and isinstance(base.comparators[0],ast.Constant) and base.comparators[0].value==0:
                inv ^= isinstance(base.ops[0],ast.Eq);base=base.left
            if self.var_guards and isinstance(base,ast.Name):
                r=self.variable(frame,base.id);label=self.fresh('smallguard')
                # Preserve the source variable. No operand copy and no temporary
                # result remain live while compiling either successor.
                if isinstance(node,ast.If):
                    y=self.block(frame,node.body,loops);n=self.block(frame,node.orelse,loops)
                    if inv:y,n=n,y
                    ans += [self.label(label,[[r.decnz,[r.inc,y,'break_'+label]],n])]
                else:
                    if node.orelse:raise ValueError('while else')
                    body=self.block(frame,node.body,loops+(label,))
                    if not inv:code=[r.decnz,[r.inc,body,'continue_'+label]]
                    else:code=[[r.decnz,[r.inc,'break_'+label]],[body,'continue_'+label]]
                    ans += [self.label(label,code)]
            else:ans += super().block(frame,[node],loops)
        return ans
