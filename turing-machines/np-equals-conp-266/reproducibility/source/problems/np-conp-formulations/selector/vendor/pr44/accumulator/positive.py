"""Conservative syntactic positivity proof; no unchecked caller assertions."""
import ast
from intrinsics import IntrinsicBuilder
from assigned_natural import assignment_certificate
from TMBuilder import subroutine

def positivity(function):
 missing=set(assignment_certificate(function)['read_before_assignment'])
 params={a.arg for a in function.args.args};writes={}
 def add(name,kind,value):writes.setdefault(name,[]).append((kind,value))
 for node in ast.walk(function):
  if isinstance(node,ast.Assign):
   if len(node.targets)!=1:raise ValueError('one assignment target required')
   t=node.targets[0]
   if isinstance(t,ast.Name):add(t.id,'assign',node.value)
   elif isinstance(t,ast.Tuple) and isinstance(node.value,ast.Tuple) and len(t.elts)==len(node.value.elts):
    for x,y in zip(t.elts,node.value.elts):add(x.id,'assign',y)
   else:raise ValueError('unsupported tuple assignment')
  elif isinstance(node,ast.AugAssign):add(node.target.id,type(node.op).__name__,node.value)
 lower={}
 def bound(node):
  if isinstance(node,ast.Constant) and isinstance(node.value,(int,bool)):return max(0,int(node.value))
  if isinstance(node,ast.Name):return lower.get(node.id,0)
  if isinstance(node,ast.BinOp):
   a,b=bound(node.left),bound(node.right)
   if isinstance(node.op,ast.Add):return a+b
   if isinstance(node.op,ast.Mult):return a*b
   if isinstance(node.op,ast.Sub) and isinstance(node.right,ast.Constant):return max(0,a-int(node.right.value))
   if isinstance(node.op,ast.Pow):return 1 if a>=1 or isinstance(node.right,ast.Constant) and node.right.value==0 else 0
   if isinstance(node.op,ast.FloorDiv) and isinstance(node.right,ast.Constant) and node.right.value>0:return a//node.right.value
  return 0
 # Only add new positive invariants. Starting from no invariant, each invariant
 # is founded by positive assignments, and all updates preserve it.
 changed=True
 while changed:
  changed=False
  for name,actions in writes.items():
   if name in lower or name in params or name in missing:continue
   assignments=[bound(value) for op,value in actions if op=='assign']
   if not assignments or min(assignments)<1:continue
   base=min(assignments);valid=True
   for op,value in actions:
    if op in ('assign','Add'):continue
    if op=='Mult' and bound(value)>=1:continue
    if op=='Pow' and base==1:continue
    valid=False;break
   if valid:lower[name]=base;changed=True
 checked=[]
 for node in ast.walk(function):
  if isinstance(node,(ast.BinOp,ast.AugAssign)) and isinstance(node.op,(ast.FloorDiv,ast.Mod)):
   divisor=node.right if isinstance(node,ast.BinOp) else node.value
   n=bound(divisor)
   if n<1:raise ValueError('divisor positivity not proved: '+ast.unparse(divisor))
   checked.append(dict(line=node.lineno,expression=ast.unparse(divisor),lower_bound=n))
 return dict(variables=dict(sorted(lower.items())),divisors=checked)

class PositiveBuilder(IntrinsicBuilder):
 def __init__(self,*args,**kw):
  super().__init__(*args,**kw)
  self.positivity_certificates={name:positivity(f) for name,f in self.functions.items()}
 @subroutine
 def division_preserve_base(self):
  a,b,q,r,c=self.micro
  return [self.copy(c,b),self.while_decnz(a,[r.inc,self.dec(c),self.if_zero(c,[q.inc,self.clear(r),self.copy(c,b)])]),self.clear(c)]
 @subroutine
 def term_kernel(self):
  a,b,q,r,c=self.micro;d=self.index_reg
  return [self.label('term',[d.decnz,[[d.decnz,[self.digit_kernel(),'break_term']],[self.dec(b),self.move(r,b),self.clear(a)]]]),self.clear(a),self.clear(b)]
