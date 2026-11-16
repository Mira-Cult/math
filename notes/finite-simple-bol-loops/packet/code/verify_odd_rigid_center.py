#!/usr/bin/env python3
"""F3 arithmetic control for the rigid-center candidate; no loop enumeration."""
P=3
B=[[[0,0,0,0],[0,0,0,1],[0,0,0,0],[0,2,0,0]],[[0,0,0,2],[0,1,1,0],[0,1,0,0],[2,0,0,0]],[[0,2,1,1],[1,1,0,2],[2,2,0,0],[0,1,0,0]]]
R=[[1,1,0,0],[0,1,0,0],[0,0,1,1],[0,0,0,1]]
T=[[1,0,0],[1,1,0],[0,1,1]]
S=[[1,0,0],[0,2,0],[0,1,1]]
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b)))%P for j in range(len(b[0]))] for i in range(len(a))]
def tr(a):return [list(x) for x in zip(*a)]
def add(*m):return [[sum(a[i][j] for a in m)%P for j in range(len(m[0][0]))]for i in range(len(m[0]))]
def mul(a,k):return [[v*k%P for v in r] for r in a]
def eye(n):return [[int(i==j) for j in range(n)]for i in range(n)]
def det(A):
 a=[r[:] for r in A]; d=1
 for i in range(len(a)):
  k=next((j for j in range(i,len(a)) if a[j][i]%P),None)
  if k is None:return 0
  if i!=k:a[i],a[k]=a[k],a[i];d=-d
  t=a[i][i]%P;d=d*t%P;inv=pow(t,-1,P)
  for j in range(i+1,len(a)):
   z=a[j][i]*inv%P;a[j]=[(a[j][k]-z*a[i][k])%P for k in range(len(a))]
 return d%P
assert mm(S,S)==eye(3)
assert mm(mm(S,T),S)==mm(T,T)
Rinv=mm(R,R)
for k in range(3):
 assert add(*[mul(B[j],S[k][j]) for j in range(3)],tr(B[k]))==[[0]*4 for _ in range(4)]
 assert mm(mm(tr(R),B[k]),Rinv)==add(*[mul(B[j],T[k][j])for j in range(3)])
assert det(B[1])==1
assert B[0][0]==[0]*4 and B[0][2]==[0]*4
assert det(add(B[2],mul(tr(B[2]),-1)))==1
D=add(B[2],mul(B[0],-1))
assert det(add(D,mul(tr(D),-1)))==0
# Coefficient positions certify linear independence of B0,B1,B2.
coeff=[[B[k][i][j] for k in range(3)] for i,j in [(1,3),(0,3),(0,2)]]
assert det(coeff)!=0
def mv(a,v):
 return [sum(x*y for x,y in zip(row,v))%P for row in a]
def power(a,k):
 out=eye(len(a))
 for _ in range(k):out=mm(out,a)
 return out
def plus(x,y):return [(a+b)%P for a,b in zip(x,y)]
def scaled(x,k):return [a*k%P for a in x]
f1=[1,2,1]
f=[[0,0,0]]
for k in range(9):f.append(plus(f[-1],mv(power(T,k),f1)))
assert f[3]==[0,0,1] and f[6]==[0,0,2] and f[9]==[0,0,0]
for k in range(9):
 assert mv(mm(power(T,k),S),f[k])==f[k]
 negative=[0,1,(1-k)%3]
 assert plus(mv(S,negative),mv(power(T,(-k)%3),negative))==[0,0,0]
 for j in range(9):
  if (k+j)%3==0:
   assert mv(power(T,k),[0,1,(1-j)%3])==negative
for level,want in [(0,1),(1,3),(2,3),(3,9)]:
 def contains(v):return all(v[i]==0 for i in range(3-level))
 assert sum(contains(v) for v in f[:9])==want
z=[0,1,1]
shift=plus(z,scaled(mv(T,z),-1))
assert shift==[0,0,2]
M=[[1,0,0],[0,1,0],[2,0,1]]
assert mv(M,f1)==plus(f1,shift) and mm(M,T)==mm(T,M) and mm(M,S)==mm(S,M)
assert pow(3,18,19)==1 and all(pow(3,j,19)!=1 for j in range(1,18))
assert pow(4,9,19)==1 and all(pow(4,j,19)!=1 for j in range(1,9))
assert pow(4,3,19)==7
# Actual three-coordinate subloop witness; u is a two-dimensional vector.
def product(x,y):
 u,t,s=x; v,r,h=y
 gamma=(u[0]*v[1]-u[1]*v[0])%19
 return (tuple((u[i]+pow(7,t,19)*v[i])%19 for i in range(2)),(t+r)%3,(s+h-gamma)%19)
X=((0,0),1,0);Y=((1,0),0,0);Z=((0,1),0,0)
left=product(product(X,Y),product(Z,X))
right=product(product(X,product(Y,Z)),X)
assert left[-1]==12 and right[-1]==18
assert left!=right
print('rigid-center arithmetic passed; direct Moufang central values: 12 and 18')
