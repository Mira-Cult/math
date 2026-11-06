"""Whole radix-digit operations: no computed power required for a lookup."""
from consuming import ConsumingDictionary
from TMBuilder import subroutine
import ast
class DigitBuilder(ConsumingDictionary):
    def __init__(self,*a,digits=True,term_lookup=False,**kw):
        super().__init__(*a,**kw)
        self.digits=digits;self.term_lookup=term_lookup;self.index_reg=self.reg('$digit.index');self.digit_certificate=[]
    @subroutine
    def division_preserve_base(self):
        a,b,q,r,c=self.micro
        return [self.if_nz(b,[self.copy(c,b),self.while_decnz(a,[r.inc,self.dec(c),
          self.if_zero(c,[q.inc,self.clear(r),self.copy(c,b)])])]),self.move(r,a),self.clear(c)]
    @subroutine
    def division_kernel(self):
        return [self.division_preserve_base(),self.clear(self.micro[1])]
    @subroutine
    def digit_kernel(self):
        a,b,q,r,c=self.micro;d=self.index_reg
        return [self.label('digitloop',[self.division_preserve_base(),
          [d.decnz,[self.clear(r),self.move(a,q),'continue_digitloop']]]),self.clear(q),self.clear(b)]
    @subroutine
    def term_kernel(self):
        a,b,q,r,c=self.micro;d=self.index_reg
        # The full arithmetic expression is also defined at base zero.
        return [self.label('positive',[
            self.if_zero(b,[self.clear(a),self.clear(d),'break_positive']),
            self.label('term',[d.decnz,
                [[d.decnz,[self.digit_kernel(),'break_term']],
                 [self.dec(b),self.move(r,b),self.clear(a)]]])]),
            self.clear(a),self.clear(b)]
    @staticmethod
    def pattern(node):
        # This rewrite removes repeated base evaluation; do not change effects.
        if any(isinstance(x,ast.Call) for x in ast.walk(node)):return None
        if not(isinstance(node,ast.BinOp) and isinstance(node.op,ast.Mod) and isinstance(node.left,ast.BinOp)
           and isinstance(node.left.op,ast.FloorDiv) and isinstance(node.left.right,ast.BinOp)
           and isinstance(node.left.right.op,ast.Pow)):
            return None
        a,p=node.left.left,node.left.right
        if ast.dump(p.left)!=ast.dump(node.right):return None
        return a,p.left,p.right
    @staticmethod
    def term_pattern(a,base):
        # base*(base-1+base*assignment)
        if not(isinstance(a,ast.BinOp) and isinstance(a.op,ast.Mult) and ast.dump(a.left)==ast.dump(base)):return None
        v=a.right
        if not(isinstance(v,ast.BinOp) and isinstance(v.op,ast.Add)):return None
        x,y=v.left,v.right
        if not(isinstance(x,ast.BinOp) and isinstance(x.op,ast.Sub) and ast.dump(x.left)==ast.dump(base)
         and isinstance(x.right,ast.Constant) and x.right.value==1):return None
        if not(isinstance(y,ast.BinOp) and isinstance(y.op,ast.Mult) and ast.dump(y.left)==ast.dump(base)):return None
        return y.right
    def expression(self,frame,node):
        pattern=self.pattern(node) if self.digits else None
        if not pattern:return super().expression(frame,node)
        a,b,d=pattern
        # Both specializations include the inherited zero-divisor convention.
        term=self.term_pattern(a,b) if self.term_lookup else None
        if term is not None:a=term
        code=[];values=[]
        for node_ in (a,b,d):
            part,v=self.operand(frame,node_);code+=part;values.append(v)
        A,B,Q,R,C=self.micro
        for target,v in zip((A,B,self.index_reg),values):code+=self.load_operand(target,v)
        for kind,value in values:
            if kind=='owned':self.free(frame,value)
        code += [self.term_kernel() if term is not None else self.digit_kernel()]
        out=self.alloc(frame);code += [self.move(out,R)]
        self.digit_certificate.append({'line':getattr(node,'lineno',None),'kind':'term' if term is not None else 'digit'})
        return code,out
