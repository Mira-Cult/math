from itertools import combinations, product
from math import factorial, comb
def count(n,edges,p,selector=lambda x:True):
 D=[[] for _ in range(n)]
 for a,b in edges:D[a].append(b);D[b].append(a)
 def dfs(x,S):
  if len(x)==p:return int(x[0]<x[-1] and selector(x))
  return sum(dfs(x+[v],S|1<<v) for v in D[x[-1]] if not S>>v&1)
 return sum(dfs([i],1<<i) for i in range(n))
K=list(combinations(range(5),2))
N=[v for k in (1,2) for v in combinations(range(5),k)]
maxima=[0]*7
for X in N:
 E=K+[(5,i) for i in X]
 maxima[0]=max(maxima[0],count(6,E,6))
 maxima[1]=max(maxima[1],count(7,E+[(5,6)],6,lambda q:5 in q and 6 in q))
 for Y in N:
  E2=E+[(6,i) for i in Y]
  maxima[2]=max(maxima[2],count(7,E2,6,lambda q:5 in q and 6 in q))
  maxima[3]=max(maxima[3],count(8,E2+[(5,7)],6,lambda q:all(z in q for z in (5,6,7))))
  maxima[4]=max(maxima[4],count(9,E2+[(5,7),(6,8)],6,lambda q:all(z in q for z in (5,6,7,8))))
  for Z in N:
   E3=E2+[(7,i) for i in Z]
   maxima[5]=max(maxima[5],count(8,E3,6,lambda q:all(z in q for z in (5,6,7))))
   maxima[6]=max(maxima[6],count(9,E3+[(5,8)],6,lambda q:all(z in q for z in (5,6,7,8))))
assert all(a<=b for a,b in zip(maxima,(72,48,88,22,4,36,4))),maxima
for n in range(6,13):
 F=12*(n-3)*(n-4)*(n-5)
 J=[(i,j) for i in range(3) for j in range(i+1,n)]
 assert count(n,J,6)==F and count(n,J,8)==0
 r=n-6;E=list(combinations(range(6),2))+[(i,j) for i in range(2) for j in range(6,n)]
 assert count(n,E,6)==360+336*r+72*comb(r,2)
print('C5 enlarged local maxima (vs 72,48,88,22,4,36,4):',maxima)
print('Replayed both exact join and C6 envelope formulas at orders 6 through 12')
