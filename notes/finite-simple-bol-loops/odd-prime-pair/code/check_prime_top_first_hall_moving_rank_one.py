"""Literal first-axis BCH and physical-row verification for the q=13 rank-one construction."""
from itertools import product
F=list(product(range(3),repeat=3));z=(0,0,0);one=(1,0,0)
def add(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def sm(k,a):return tuple(k*x%3 for x in a)
def neg(a):return sm(-1,a)
def mul(a,b):
 t=[0]*5
 for i,j in product(range(3),repeat=2):t[i+j]+=a[i]*b[j]
 for i in (4,3):t[i-3]+=t[i];t[i-2]+=t[i]
 return tuple(x%3 for x in t[:3])
def frob(a):
 return mul(mul(a,a),a)
R=[{a:a for a in F},{a:frob(a) for a in F},{a:frob(frob(a)) for a in F}]
assert all(frob(R[2][a])==a for a in F)
def trace(a):
 s=add(a,add(R[1][a],R[2][a]))
 assert s[1:]==(0,0)
 return s[0]
def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
ll=next(ell for ell in F if all(dot(ell,add(R[1][a],neg(a)))==trace(a) for a in F))
def lam(a):return dot(ll,a)
# First axis together with scalar c. The second axis is signed reciprocal,
# and does not enter a first-axis conjugacy obstruction.
def op(g,h):
 v,f,c=g;w,k,d=h
 return add(v,w),add(add(f,k),sm(2,add(sm(c,w),sm(-d,v)))),(c+d)%3
def inv(g):v,f,c=g;return neg(v),neg(f),-c%3
def rot(g,j):
 v,f,c=g;j%=3
 return R[j][v],R[j][f],c
def prod(g,h):
 a,j=g;b,k=h
 return op(a,rot(b,j)),(j+k)%3
W={(v,f,trace(v)) for v,f in product(F,repeat=2) if trace(f)==lam(v)}
assert len(W)==3**5
assert all(op(a,b) in W for a,b in product(W,repeat=2))
fu=next(f for f in F if trace(f)==1)
u=(z,fu,1);h1=(u,1);h2=prod(h1,h1)
assert prod(h1,h2)[0] in W
for w in W:
 assert op(op(u,rot(w,1)),inv(u)) in W
count=0
for j,hj in ((1,h1),(2,h2)):
 for w in W:
  (v,f,c),top=prod((w,0),hj)
  assert top==j
  if trace(v):continue
  assert c==j and trace(f)==(lam(v)+j)%3
  for k in range(3):
   g0=rot(inv((v,f,c)),k-j)
   for w1,g1,d in product(F,F,range(3)):
    # compare only conjugators whose first V-coordinate becomes 0
    if add(w1,add(g0[0],neg(R[-j%3][w1])))!=z:continue
    n=(w1,g1,d)
    a=op(op(n,g0),rot(inv(n),-j))
    assert a[0]==z and trace(a[1])!=0
    count+=1
assert count==2*81*3*3*27*3
print("physical W closure, actual top closure, nonzero conjugation trace:",count)
print("loop order",13*3**8)
