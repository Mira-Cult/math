from itertools import product
from random import Random
p = 3
masks = range(1, 8)
basis = tuple(tuple(int(i == j) for i in masks) for j in masks)

def add(u, v):
    return tuple((a+b) % p for a,b in zip(u,v))
def scale(c, u):
    return tuple(c*a % p for a in u)
def mul(u,v):
    w = [0]*7
    for a,b in product(masks, repeat=2):
        if a & b: continue
        sign = (-1)**sum((a>>i)&(b>>j)&1 for i in range(3) for j in range(i))
        if a.bit_count() == 1 and b.bit_count() == 2:
            sign = -sign
        w[(a|b)-1] += sign*u[a-1]*v[b-1]
    return tuple(z % p for z in w)
def star(u,v):
    return add(add(u,v),mul(u,v))
rng = Random(342)
for x,y,z in product(basis, repeat=3):
    assert mul(mul(x,y),z) == scale(-1,mul(x,mul(y,z)))
x,y,z = basis[0],basis[1],basis[3]
assert star(star(x,y),z) != star(x,star(y,z))
signature = lambda x: tuple(mul(x,y) for y in basis)
assert len({signature(a) for a in product(range(p), repeat=7)}) == p**6
for _ in range(500):
    x,y,z = [tuple(rng.randrange(p) for _ in masks) for j in range(3)]
    assert star(star(x, y), star(z, x)) == star(x, star(star(y,z),x))
    assert star(scale(2,star(x,y)),scale(2,star(y,x))) == add(x,y)
    affine = add(z, mul(x,z))
    # In F3 x/2 = 2x. Apply the two genuine loop translations L_{x/2}, R_{x/2}^{-1}.
    u = scale(2,x)
    lu = star(u,z)
    candidate = add(add(lu,scale(-1,u)),mul(u,lu))
    assert candidate == affine
print("Exact basis anti-associativity, nonassociative triple, 729 distinct linear parts, and 500 Moufang and term controls passed.")
