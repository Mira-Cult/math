"""Experimental smaller arithmetic kernels over the inherited natural grammar."""
from pathlib import Path
import sys,ast
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'accumulator'),str(ROOT/'continuation'),str(ROOT/'shared')]
from positive import PositiveBuilder
from intrinsics import IntrinsicBuilder
from TMBuilder import subroutine


class KernelMixin:
    def __init__(self,*args,compact_equal=True,countdown_division=True,
                 copy_order='original',refactor_options=None,shared_selector=False,
                 fused_consuming=False,intrinsic_sites=(),**kwargs):
        super().__init__(*args,**kwargs)
        self.compact_equal=compact_equal
        self.countdown_division=countdown_division
        self.copy_order=copy_order
        self.refactor_options=refactor_options
        self.shared_selector=shared_selector
        self.fused_consuming=fused_consuming
        self.fused_consuming_certificate=[]
        self.intrinsic_sites=frozenset(intrinsic_sites)
        self.possible_intrinsic_sites={}

    def small_pattern(self,node):
        key=f"{getattr(node,'lineno',None)}:{getattr(node,'col_offset',None)}:{type(node).__name__}"
        flags=('small_ops','small_compare','small_power','small_half')
        saved=[getattr(self,k) for k in flags]
        try:
            for k in flags:setattr(self,k,True)
            pattern=super().small_pattern(node)
        finally:
            for k,v in zip(flags,saved):setattr(self,k,v)
        if pattern is not None:
            self.possible_intrinsic_sites[key]=dict(expression=ast.unparse(node),
                operation=pattern[1],constant=pattern[2])
        return pattern if key in self.intrinsic_sites else super().small_pattern(node)

    def block(self,frame,statements,loops=()):
        if not self.fused_consuming:return super().block(frame,statements,loops)
        code=[]
        for node in statements:
            match=False
            if (isinstance(node,ast.Assign) and len(node.targets)==1 and
                isinstance(node.targets[0],ast.Tuple) and isinstance(node.value,ast.Tuple)):
                ts,vs=node.targets[0].elts,node.value.elts
                match=(len(ts)==len(vs)==2 and all(isinstance(t,ast.Name) for t in ts)
                    and ts[0].id!=ts[1].id
                    and isinstance(vs[0],ast.BinOp) and isinstance(vs[1],ast.BinOp)
                    and isinstance(vs[0].op,ast.Mod) and isinstance(vs[1].op,ast.FloorDiv)
                    and isinstance(vs[0].left,ast.Name) and isinstance(vs[1].left,ast.Name)
                    and vs[0].left.id==vs[1].left.id
                    and ast.dump(vs[0].right)==ast.dump(vs[1].right)
                    and not any(isinstance(x,ast.Call) for x in ast.walk(vs[0].right)))
            if not match:
                code+=super().block(frame,[node],loops);continue
            left,right=vs[0].left,vs[0].right
            src=self.variable(frame,left.id)
            consume=left.id in {t.id for t in ts}
            # Compute a complex divisor before consuming its old input cell.
            # operand(Name) is deferred, so snapshot a self-divisor first.
            part,b=self.operand(frame,right)
            a=('consume' if consume else 'reference',src)
            A,B,Q,R,C=self.micro
            alias=b[0] in ('reference','consume') and b[1]==src
            if alias:
                part+=self.load_operand(B,('reference',src))+self.load_operand(A,a)
            else:
                part+=self.load_operand(A,a)+self.load_operand(B,b)
            part+=[self.division_kernel()]
            if b[0]=='owned':self.free(frame,b[1])
            targets=[self.variable(frame,t.id) for t in ts]
            for target,result in zip(targets,(R,Q)):
                if not(consume and target==src):part+=[self.clear(target)]
                part+=[self.move(target,result)]
            code+=part
            self.fused_consuming_certificate.append(dict(function=frame['name'],
                line=getattr(node,'lineno',None),dividend=left.id,divisor=ast.unparse(right),
                targets=[t.id for t in ts],consumed=consume,
                divisor_pure=True,complex_divisor_evaluated_before_consumption=True,
                self_divisor_snapshotted_first=alias))
        return code

    @subroutine
    def equality_kernel(self):
        if not self.compact_equal:
            return super().equality_kernel()
        a,b,q,r,c=self.micro
        return [self.label('eq',[
            self.label('pairs',[a.decnz,[[b.decnz,'continue_pairs'],
                [self.clear(a),'break_eq']]]),
            self.if_zero(b,q.inc)]),self.clear(b)]

    @subroutine
    def division_preserve_base(self):
        if not self.countdown_division:
            return super().division_preserve_base()
        a,b,q,r,c=self.micro
        return [self.dec(b),self.copy(c,b),self.while_decnz(a,
            self.label('unit',[[c.decnz,[r.inc,'break_unit']],
                [q.inc,self.clear(r),self.copy(c,b)]])),
            b.inc,self.clear(c)]

    @subroutine
    def copy(self,out,x):
        if self.copy_order=='original':return super().copy(out,x)
        assert len({out,x,self.scratch})==3
        if self.copy_order=='swap':
            return [self.while_decnz(x,[self.scratch.inc,out.inc]),self.move(x,self.scratch)]
        if self.copy_order=='restore':
            return [self.move(self.scratch,x),self.while_decnz(self.scratch,[out.inc,x.inc])]
        if self.copy_order=='restore-swap':
            return [self.move(self.scratch,x),self.while_decnz(self.scratch,[x.inc,out.inc])]
        raise ValueError(self.copy_order)

    def build_tree(self):
        super().build_tree()
        if self.refactor_options is not None:
            from closed_sequences import refactor
            refactor(self,**self.refactor_options)
        return self

    def build_machine(self):
        super().build_machine()
        if self.shared_selector:
            sys.path.insert(0,str(ROOT/'compression/compiler'))
            from shared_selector import apply
            self.selector_certificate=apply(self)
        return self


class KernelBuilder(KernelMixin,PositiveBuilder):
    """Selected compiler: inherited positivity proof admits countdown division."""


class GenericKernelBuilder(KernelMixin,IntrinsicBuilder):
    """Generic counterpart retains the inherited zero-divisor convention."""
    def __init__(self,*args,countdown_division=False,**kwargs):
        if countdown_division:
            raise ValueError('countdown division requires the positive-divisor proof')
        super().__init__(*args,countdown_division=False,**kwargs)
