#!/usr/bin/env python3
"""Exact checker for C(x,y)=f(x,L_y^{-1}(x)) on a quasigroup."""
W={
  13:(1,9,11,2,8,7,3,0,6,12,10,5,4),
  17:(1,0,9,6,10,15,3,16,12,5,4,11,14,8,2,13,7),
  25:(1,14,12,2,19,0,22,9,17,13,18,3,5,7,21,11,16,6,15,24,23,8,20,4,10),
}

def f_at(m,w,x,y):
    if x==m:
        return m if y==m else (y+1)%m
    if y==m:
        return (x+1)%m
    if x==y:
        return m
    return (x+w[(y-x)%m])%m

def main():
    tables = {m+1:[[f_at(m,w,x,y) for y in range(m+1)] for x in range(m+1)]
              for m,w in W.items()}
    a14=tables[14]
    tables[42]=[[3*a14[x//3][y//3]+((x%3+y%3)%3)
                 for y in range(42)] for x in range(42)]
    for n,f in sorted(tables.items()):
        core=[[f[x][f[y].index(x)] for y in range(n)] for x in range(n)]
        square=[[f[f[x][y]][y] for y in range(n)] for x in range(n)]
        for a in (f,core,square):
            assert all(sorted(r)==list(range(n)) for r in a)
            assert all(sorted(r)==list(range(n)) for r in zip(*a))
        print(n, "squared column row 0:", square[0])
        print(n, "core row 0:", core[0])
        print(n, "core column 0:",list(zip(*core))[0])
        print(n, "PASS: Latin multiplication, explicit division core, and squared right translations")

if __name__=="__main__":
    main()
