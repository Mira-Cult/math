"""Conservative structured backwards liveness with per-Name last-read markers.

This pass never changes the parsed AST. It returns a set of object identities
for reads whose source cell may be consumed instead of copied. Loop analysis
uses a monotone least fixed point; break/continue have explicit successors.
"""
import ast

def names(node):
    return {n.id for n in ast.walk(node) if isinstance(n,ast.Name) and isinstance(n.ctx,ast.Load)}

class Liveness:
    def __init__(self):self.consume=set();self.cert=[]
    def expr(self,node,after,mark=False):
        after=set(after)
        if isinstance(node,ast.Name):
            if isinstance(node.ctx,ast.Load):
                if mark and node.id not in after:self.consume.add(id(node));self.cert.append({'name':node.id,'line':getattr(node,'lineno',None),'column':getattr(node,'col_offset',None)})
                after.add(node.id)
            return after
        if isinstance(node,ast.Constant):return after
        if isinstance(node,ast.BinOp):return self.expr(node.left,self.expr(node.right,after,mark),mark)
        if isinstance(node,ast.Compare):
            for c in reversed(node.comparators):after=self.expr(c,after,mark)
            return self.expr(node.left,after,mark)
        if isinstance(node,(ast.Tuple,ast.List)):
            for v in reversed(node.elts):after=self.expr(v,after,mark)
            return after
        if isinstance(node,ast.UnaryOp):return self.expr(node.operand,after,mark)
        if isinstance(node,ast.BoolOp):
            for v in reversed(node.values):after=self.expr(v,after,mark)
            return after
        # Unknown effectful expressions are rejected by the selected compiler;
        # conservatively do not consume any of their reads.
        return after|names(node)
    def block(self,statements,after,break_live=None,continue_live=None,mark=False):
        live=set(after)
        for s in reversed(statements):
            if isinstance(s,ast.Assign):
                defs={n.id for t in s.targets for n in ast.walk(t) if isinstance(n,ast.Name)}
                live=self.expr(s.value,live-defs,mark)
            elif isinstance(s,ast.AugAssign) and isinstance(s.target,ast.Name):
                live=self.expr(s.value,(live-{s.target.id})|{s.target.id},mark)
            elif isinstance(s,ast.If):
                y=self.block(s.body,live,break_live,continue_live,mark)
                n=self.block(s.orelse,live,break_live,continue_live,mark)
                live=self.expr(s.test,y|n,mark)
            elif isinstance(s,ast.While):
                if s.orelse:raise ValueError('while-else not supported')
                tail=set(live);head=tail|names(s.test)
                while True:
                    body=self.block(s.body,head,tail,head,False)
                    new=tail|names(s.test)|body
                    if new==head:break
                    assert head<=new
                    head=new
                body=self.block(s.body,head,tail,head,mark)
                self.expr(s.test,tail|body,mark)
                live=head
            elif isinstance(s,ast.Break):
                if break_live is None:raise ValueError('break outside loop')
                live=set(break_live)
            elif isinstance(s,ast.Continue):
                if continue_live is None:raise ValueError('continue outside loop')
                live=set(continue_live)
            elif isinstance(s,ast.Return):live=self.expr(s.value,set(),mark) if s.value else set()
            elif isinstance(s,ast.Expr):
                if not(isinstance(s.value,ast.Call) and isinstance(s.value.func,ast.Name) and s.value.func.id=='beep'):
                    live=self.expr(s.value,live,False)
            elif isinstance(s,ast.Pass):pass
            else:raise ValueError('unsupported statement '+ast.dump(s))
        return live
    def run(self,functions):
        for f in functions.values():self.block(f.body,set(),mark=True)
        return self
