"""Shared, fixed-register arithmetic; no implicit interpreter or runtime.

The eighteen inherited backend modules remain unchanged. This extension emits
only their existing INC/DECNZ/structured-control grammar. Five globally reserved
registers are empty at each complete-expression and statement boundary.
"""
from __future__ import annotations
import ast
if not __debug__:
    raise RuntimeError("compiler checks require assertions enabled")
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'shared'))
from literal_assign import LiteralAssignBuilder
from TMBuilder import subroutine


class StreamedArithmeticBuilder(LiteralAssignBuilder):
    def __init__(self,*args,stream_compare=True,stream_small=True,**kwargs):
        super().__init__(*args,**kwargs)
        self.stream_compare=stream_compare
        self.stream_small=stream_small
        self.micro=tuple(self.reg('$micro.'+x) for x in ('a','b','q','r','c'))
        self.guard_certificate=[]

    @subroutine
    def division_kernel(self):
        a,b,q,r,c=self.micro
        return [self.if_nz(b,[self.copy(c,b),
            self.while_decnz(a,[r.inc,self.dec(c),
                self.if_zero(c,[q.inc,self.clear(r),self.copy(c,b)])])]),
            self.move(r,a),self.clear(b),self.clear(c)]

    @subroutine
    def product_kernel(self):
        a,b,q,r,c=self.micro
        return [self.while_decnz(b,self.copy(q,a)),self.clear(a)]

    @subroutine
    def power_kernel(self):
        a,b,q,r,c=self.micro
        return [q.inc,self.while_decnz(b,[
            self.while_decnz(q,self.copy(r,a)),self.move(q,r)]),self.clear(a)]

    @subroutine
    def equality_kernel(self):
        a,b,q,r,c=self.micro
        return [self.label('eq',[self.while_decnz(a,[
            self.if_zero(b,[self.clear(a),'break_eq']),self.dec(b)]),
            self.if_zero(b,q.inc)]),self.clear(b)]

    @subroutine
    def half_kernel(self):
        a,b,q,r,c=self.micro
        return [self.while_decnz(a,[r.inc,self.if_decnz(a,[self.clear(r),q.inc])])]

    @subroutine
    def minus_kernel(self):
        a,b,q,r,c=self.micro
        return [self.while_decnz(b,self.dec(a))]

    @subroutine
    def truth_kernel(self):
        a,b,q,r,c=self.micro
        return [self.if_decnz(a,[q.inc,self.clear(a)])]

    @subroutine
    def less_kernel(self):
        a,b,q,r,c=self.micro
        return [self.while_decnz(a,self.dec(b)),self.if_decnz(b,[q.inc,self.clear(b)])]

    @subroutine
    def divmod(self,q,r,a,b,countdown):
        A,B,Q,R,C=self.micro
        return [self.move(A,a),self.move(B,b),self.division_kernel(),
                self.move(q,Q),self.move(r,R)]

    @subroutine
    def multiply(self,out,a,b):
        A,B,Q,R,C=self.micro
        return [self.move(A,a),self.move(B,b),self.product_kernel(),self.move(out,Q)]

    @subroutine
    def power(self,out,a,b,work):
        A,B,Q,R,C=self.micro
        return [self.move(A,a),self.move(B,b),self.power_kernel(),self.move(out,Q)]

    @subroutine
    def equal(self,out,a,b):
        A,B,Q,R,C=self.micro
        return [self.move(A,a),self.move(B,b),self.equality_kernel(),self.move(out,Q)]

    @subroutine
    def halve(self,q,r,a):
        A,B,Q,R,C=self.micro
        return [self.move(A,a),self.half_kernel(),self.move(q,Q),self.move(r,R)]

    @subroutine
    def double_constant_register(self,out,work):
        return [self.while_decnz(out,[work.inc,work.inc]),self.move(out,work)]

    def operand(self,frame,node):
        if isinstance(node,ast.Name):
            return [],('reference',self.variable(frame,node.id))
        if isinstance(node,ast.Constant) and isinstance(node.value,(int,bool)) and node.value>=0:
            return [],('constant',int(node.value))
        code,value=self.expression(frame,node)
        return code,('owned',value)

    def load_operand(self,target,value):
        kind,data=value
        if kind=='reference':return [self.copy(target,data)]
        if kind=='owned':return [self.move(target,data)]
        C=self.micro[4]
        code=[]
        for bit in bin(data)[2:]:
            if code:code += [self.double_constant_register(target,C)]
            if bit=='1':code += [target.inc]
        return code

    def expression(self,frame,node):
        if isinstance(node,ast.Constant) and type(node.value) is int and node.value>4:
            out,work=self.alloc(frame),self.alloc(frame)
            code=[]
            for bit in bin(node.value)[2:]:
                if code:code += [self.double_constant_register(out,work)]
                if bit=='1':code += [out.inc]
            self.free(frame,work)
            return code,out
        compare=isinstance(node,ast.Compare) and len(node.ops)==1
        binary=isinstance(node,ast.BinOp)
        if not binary and not(compare and self.stream_compare):
            return super().expression(frame,node)
        op=node.ops[0] if compare else node.op
        left=node.left
        right=node.comparators[0] if compare else node.right
        if (not self.stream_small and isinstance(right,ast.Constant)
                and isinstance(right.value,(int,bool)) and 0<=right.value<=4):
            if compare or isinstance(op,(ast.Add,ast.Sub,ast.Mult,ast.FloorDiv,ast.Mod)):
                return super().expression(frame,node)
        if not self.stream_small and isinstance(left,ast.Constant) and left.value==2 and isinstance(op,ast.Pow):
            return super().expression(frame,node)
        code,a=self.operand(frame,left)
        more,b=self.operand(frame,right);code+=more
        A,B,Q,R,C=self.micro
        code += self.load_operand(A,a)+self.load_operand(B,b)
        for kind,value in (a,b):
            if kind=='owned':self.free(frame,value)
        out=self.alloc(frame)
        result=Q
        if isinstance(op,ast.Add):code += [self.move(A,B)];result=A
        elif isinstance(op,ast.Sub):code += [self.minus_kernel()];result=A
        elif isinstance(op,ast.Mult):code += [self.product_kernel()]
        elif isinstance(op,ast.Pow):code += [self.power_kernel()]
        elif isinstance(op,(ast.FloorDiv,ast.Mod)):
            code += [self.division_kernel()]
            if isinstance(op,ast.Mod):code += [self.clear(Q)];result=R
            else:code += [self.clear(R)]
        elif isinstance(op,(ast.Eq,ast.NotEq)):
            code += [self.equality_kernel()]
            if isinstance(op,ast.NotEq):
                code += [self.if_zero(Q,A.inc),self.clear(Q)];result=A
        elif isinstance(op,(ast.Lt,ast.LtE,ast.Gt,ast.GtE)):
            if isinstance(op,(ast.Gt,ast.GtE)):
                code += [self.move(Q,A),self.move(A,B),self.move(B,Q)]
            if isinstance(op,(ast.LtE,ast.GtE)):code += [B.inc]
            code += [self.less_kernel()]
        else:raise ValueError('unsupported streamed operator: '+ast.dump(op))
        code += [self.move(out,result)]
        return code,out


class DirectGuardBuilder(StreamedArithmeticBuilder):
    def direct_condition(self,frame,node):
        A,B,Q,R,C=self.micro
        if isinstance(node,ast.Compare) and len(node.ops)==1:
            code,a=self.operand(frame,node.left)
            more,b=self.operand(frame,node.comparators[0]);code+=more
            code += self.load_operand(A,a)+self.load_operand(B,b)
            for kind,value in (a,b):
                if kind=='owned':self.free(frame,value)
            op=node.ops[0];condition=Q
            if isinstance(op,(ast.Eq,ast.NotEq)):
                code += [self.equality_kernel()]
                if isinstance(op,ast.NotEq):
                    code += [self.if_zero(Q,A.inc),self.clear(Q)];condition=A
            elif isinstance(op,(ast.Lt,ast.LtE,ast.Gt,ast.GtE)):
                if isinstance(op,(ast.Gt,ast.GtE)):
                    code += [self.move(Q,A),self.move(A,B),self.move(B,Q)]
                if isinstance(op,(ast.LtE,ast.GtE)):code += [B.inc]
                code += [self.less_kernel()]
            else:raise ValueError('unsupported comparison')
            return code,condition
        code,value=self.operand(frame,node)
        code += self.load_operand(A,value)+[self.truth_kernel()]
        if value[0]=='owned':self.free(frame,value[1])
        return code,Q

    def block(self,frame,statements,loops=()):
        code=[]
        for node in statements:
            if (isinstance(node,(ast.If,ast.While)) and
                not(isinstance(node,ast.While) and isinstance(node.test,ast.Constant) and node.test.value is True)):
                if isinstance(node,ast.While) and node.orelse:raise ValueError('while else is unsupported')
                part,condition=self.direct_condition(frame,node.test)
                label=self.fresh('if' if isinstance(node,ast.If) else 'loop')
                if isinstance(node,ast.If):
                    yes=self.block(frame,node.body,loops)
                    no=self.block(frame,node.orelse,loops)
                    code += part+[self.label(label,[[condition.decnz,[yes,'break_'+label]],no])]
                else:
                    body=self.block(frame,node.body,loops+(label,))
                    code += [self.label(label,[part,[condition.decnz,[body,'continue_'+label]]])]
                self.guard_certificate.append(dict(function=frame['name'],line=getattr(node,'lineno',None),
                    guard=ast.dump(node.test),register=str(condition),direct_dictionary_guard=True))
            else:code += super().block(frame,[node],loops)
        return code


class FusedDictionaryBuilder(DirectGuardBuilder):
    def __init__(self,*args,fuse_divrem=True,forward_results=True,**kwargs):
        kwargs['stream_small']=True;kwargs['stream_compare']=True
        super().__init__(*args,**kwargs)
        self.fuse_divrem=fuse_divrem;self.forward_results=forward_results
        self.fusion_certificate=[]

    @staticmethod
    def divrem_assignment(node):
        if not(isinstance(node,ast.Assign) and len(node.targets)==1 and
               isinstance(node.targets[0],ast.Tuple) and isinstance(node.value,ast.Tuple)):return None
        targets,values=node.targets[0].elts,node.value.elts
        if len(targets)!=2 or len(values)!=2 or not all(isinstance(t,ast.Name) for t in targets):return None
        if targets[0].id==targets[1].id:return None
        r,q=values
        if not(isinstance(r,ast.BinOp) and isinstance(q,ast.BinOp) and
            isinstance(r.op,ast.Mod) and isinstance(q.op,ast.FloorDiv) and
            isinstance(r.left,ast.Name) and isinstance(q.left,ast.Name) and
            r.left.id==q.left.id and isinstance(r.right,(ast.Name,ast.Constant)) and
            ast.dump(r.right)==ast.dump(q.right)):return None
        return targets,r.left,r.right

    def block(self,frame,statements,loops=()):
        code=[]
        for node in statements:
            pair=self.divrem_assignment(node) if self.fuse_divrem else None
            if pair:
                targets,left,right=pair
                part,a=self.operand(frame,left)
                more,b=self.operand(frame,right);part+=more
                A,B,Q,R,C=self.micro
                part += self.load_operand(A,a)+self.load_operand(B,b)+[self.division_kernel()]
                for kind,value in (a,b):
                    if kind=='owned':self.free(frame,value)
                remainder,quotient=(self.variable(frame,t.id) for t in targets)
                code += part+[self.clear(remainder),self.clear(quotient),self.move(remainder,R),self.move(quotient,Q)]
                self.fusion_certificate.append(dict(function=frame['name'],line=getattr(node,'lineno',None),kind='divrem'))
            elif (self.forward_results and isinstance(node,ast.Assign) and len(node.targets)==1
                    and isinstance(node.targets[0],ast.Name) and
                    (isinstance(node.value,ast.BinOp) or isinstance(node.value,ast.Compare) and len(node.value.ops)==1)):
                value=node.value
                part,out=self.expression(frame,value)
                op=value.op if isinstance(value,ast.BinOp) else value.ops[0]
                result=self.micro[0] if isinstance(op,(ast.Add,ast.Sub,ast.NotEq)) else self.micro[3] if isinstance(op,ast.Mod) else self.micro[2]
                if not part or part[-1]!=self.move(out,result):raise ValueError('result-forwarding contract not met')
                target=self.variable(frame,node.targets[0].id)
                code += part[:-1]+[self.clear(target),self.move(target,result)]
                self.free(frame,out)
                self.fusion_certificate.append(dict(function=frame['name'],line=getattr(node,'lineno',None),kind='result-forward'))
            else:code+=super().block(frame,[node],loops)
        return code
