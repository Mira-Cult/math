import random
p=19
inv2=10
beta=lambda x,y:(x[0]*y[1]-x[1]*y[0])%p
add=lambda x,y:tuple((a+b)%p for a,b in zip(x,y))
scale=lambda c,x:tuple(c*a%p for a in x)
def mul(g,h):
 x,y,c,t,s,z=g; X,Y,C,T,S,Z=h
 X=scale(pow(7,t%3,p),X);Y=scale(pow(7,(-t)%3,p),Y)
 return (add(x,X),add(y,Y),(c+C+inv2*(beta(x,Y)+beta(y,X)))%p,(t+T)%3,(s+S)%19,(z+Z)%3)
def K(u,t,s):return (scale(-pow(7,(-t)%3,p),u),u,0,(-t)%3,(-s)%19,0)
def red(g):
 x,y,c,t,s,z=g
 # Right multiply H's first axis to zero x; central labels attached to torus shifts identify z and c.
 # Desired section with vector y and desired positive t = z-t
 T=(z-t)%3
 xx=scale(-pow(7,(-T)%3,p),y)
 # choose h first axis w to achieve target xx; h a-label -z kills central z using graph.
 # target q central 0, h central q-label k = -c - .5 beta(y,xx-x)
 k=(-c-inv2*beta(y,add(xx,scale(-1,x))))%p
 return (y,T,(-s-k)%p)
def formula(a,b):
 u,t,s=a;v,r,h=b
 return add(u,scale(pow(7,t,p),v)),(t+r)%3,(s+h-beta(u,v))%p
R=random.Random(23)
for i in range(10000):
 a=((R.randrange(p),R.randrange(p)),R.randrange(3),R.randrange(p));b=((R.randrange(p),R.randrange(p)),R.randrange(3),R.randrange(p))
 assert red(mul(K(*a),K(*b)))==formula(a,b),(a,b,red(mul(K(*a),K(*b))),formula(a,b))
print('10000 independent BCH-section product comparisons passed')
