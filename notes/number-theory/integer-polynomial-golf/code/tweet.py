E=[]
N=iter(range(3779))
class S(str):
 def __rsub__(a,b):return S(b)-a
 def __pow__(a,b):return a*a**(b-1)if b else 1
 def __neg__(a):return 0-a
 def __truediv__(a,b):
  z=v();E.append(f'({b})*{z}-1');return a*z
 def __rtruediv__(a,b):return S(b)/a
v=lambda:S(f'x{next(N)}')
def g(e):
 z=v();E.append(f'{z}-({e})');return z
for a,b in zip(("add","sub","mul"),"+-*"):exec(f"S.__{a}__=lambda a,b:g(f'({{a}}){b}({{b}})')")
S.__radd__=S.__add__;S.__rmul__=S.__mul__
class K:
 def __init__(a,x=0,y=0):a.x=S(x);a.y=S(y)
 def __add__(a,b):
  if type(b)!=K:b=K(b)
  return K(a.x+b.x,a.y+b.y)
 __radd__=__add__
 def __neg__(a):return K(-a.x,-a.y)
 def __sub__(a,b):return a+-b
 def __mul__(a,b):
  if type(b)!=K:b=K(b)
  return K(a.x*b.x+2*a.y*b.y,a.x*b.y+a.y*b.x)
 __rmul__=__mul__
 def __pow__(a,b):return a**(b-1)*a if b else K(1)
 def c(a):return K(a.x,-a.y)
 def n(a):return a.x*a.x-2*a.y*a.y
 def __truediv__(a,b):
  if type(b)!=K:b=K(b)
  t=a*b.c();d=b.n();return K(t.x/d,t.y/d)
 def __rtruediv__(a,b):return K(b)/a
def w(a):E.extend((a.x,a.y)if type(a)==K else[a])
def p():
 x=K(v(),v());y=K(v(),v());w(y*y-x**3+D*x)
 s=(x*x*3-D)/(y*2);u=s*s-x*2
 return u,s*(x-u)-y
def s(A,B):
 x,y=A;u,v=B;s=(y+v)/(x-u);z=s*s-x-u
 return z,s*(x-z)-y
def z(A):return -A[0]/A[1]
def o(b):
 e,p,q,s=[v()for i in'1234'];B=17*b;h=e*(B-b*b)
 w(p*p-B*(1-e)*(1+3*e));w(B*q*q-(s*s-B*h)*(s*s+3*B*h))
X=v();D=K(11,-6);P=K(57,-28)/8,K(-660,417)/32
Q=[p()for i in'1234'];U=[p()for i in'1234'];H=p();V=[s(H,P)]+[s(u,q)for u,q in zip(U,Q)]
B=51*X*X+2504
r=B*(B-1)*(B-2401)*(32*B+343)*(2*B-1)
R=S('149**19365')*r/(1+149**2*r)
Z=z(s(Q[1],P))/z(H);F=(1/H[0]).n()
A=(Z.x**2+R*Z.y**2)/R**4
W=(A*A+R*F*F)/R**4
o(R*(R+9792)*W*W)
L=[z(u)/z(H)for u in U]
C=[a-(z(v)/z(V[0])).c()for a,v in zip(L,V[1:])]
a,b,c,d=L
G=c*c-b*(b-2)*c*d+(b-2)**2*d*d-1
J=[1/u[0] for u in [H]+U]+[(1/u[0]).c()for u in V]
I=C+[a-B,G]
T=sum(q[0] for q in Q);l=v()
j=[S(0),S(-1)/2,S(-1),S(1)/2399,S(-32)/407]
for u in [S(1),T.x*T.x,(T.x+T.y)**2]:
 t=u*l;f=S(1)
 for h in j:f=f*(t-h)*(t-2+h)
 q=(t-1)**10/f-1
 W=K(1)
 for u,k in [(J,3),(I,5)]:
  for a in u:W=W*(1+a*a*(q**k))
 tau=W.n()/(2*W.x)
 o((S(408)/409)**2*tau*tau/(q+1))
print('+'.join(f'({e})**2'for e in E))