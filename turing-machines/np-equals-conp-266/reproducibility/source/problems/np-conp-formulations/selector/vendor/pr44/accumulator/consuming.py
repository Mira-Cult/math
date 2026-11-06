from pathlib import Path
import sys,ast
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path[:0]=[str(ROOT/'continuation'),str(ROOT/'shared')]
# Explicit import avoids the new accumulator compiler's module name.
import importlib.util
s=importlib.util.spec_from_file_location('dictionary_base',ROOT/'continuation/compiler.py')
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
from liveness import Liveness
class ConsumingDictionary(m.FusedDictionaryBuilder):
    def __init__(self,*a,consume=True,**kw):
        super().__init__(*a,**kw)
        self.live=Liveness().run(self.functions) if consume else Liveness()
        # operand(Name) is a delayed reference, not an immediate read. A later
        # nested expression must not consume a cell needed by an earlier
        # delayed reference. Restrict consumption to one read in the entire
        # simultaneous expression group (and account for augmented LHS reads).
        from collections import Counter
        rejected=set()
        for f in self.functions.values():
            for statement in ast.walk(f):
                expression=None;extra=[]
                if isinstance(statement,ast.Assign):expression=statement.value
                elif isinstance(statement,ast.AugAssign):expression=statement.value;extra=[statement.target.id]
                elif isinstance(statement,(ast.If,ast.While)):expression=statement.test
                elif isinstance(statement,ast.Return):expression=statement.value
                if expression is None:continue
                reads=[x for x in ast.walk(expression) if isinstance(x,ast.Name) and isinstance(x.ctx,ast.Load)]
                counts=Counter([x.id for x in reads]+extra)
                rejected.update(id(x) for x in reads if counts[x.id]>1)
        self.live.consume.difference_update(rejected)
        self.live.rejected_delayed_aliases=len(rejected)
        active={(n.id,getattr(n,'lineno',None),getattr(n,'col_offset',None)) for f in self.functions.values() for n in ast.walk(f) if isinstance(n,ast.Name) and id(n) in self.live.consume}
        self.live.cert=[x for x in self.live.cert if (x['name'],x['line'],x['column']) in active]
    def operand(self,frame,node):
        if isinstance(node,ast.Name) and id(node) in self.live.consume:
            return [],('consume',self.variable(frame,node.id))
        return super().operand(frame,node)
    def load_operand(self,target,value):
        if value[0]=='consume':return [self.move(target,value[1])]
        return super().load_operand(target,value)
    def expression(self,frame,node):
        if isinstance(node,ast.Name) and id(node) in self.live.consume:
            out=self.alloc(frame)
            return [self.move(out,self.variable(frame,node.id))],out
        return super().expression(frame,node)
