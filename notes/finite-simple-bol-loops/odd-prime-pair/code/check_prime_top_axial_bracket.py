"""Finite coefficient replay for compatible internal axial forms in prime top."""
from itertools import combinations

def rank_mod(rows,p):
    a=[list(row) for row in rows];r=0
    for j in range(len(a[0])):
        k=next((k for k in range(r,len(a)) if a[k][j]%p),None)
        if k is None:continue
        a[r],a[k]=a[k],a[r]
        fac=pow(a[r][j]%p,-1,p);a[r]=[x*fac%p for x in a[r]]
        for k,row in enumerate(a):
            if k==r:continue
            fac=row[j]%p
            a[k]=[(x-fac*y)%p for x,y in zip(row,a[r])]
        r+=1
    return r

for p,q in [(3,13),(5,11),(5,71),(7,29)]:
    assert pow(p,p,q)==1 and p%q!=1
    weights=[pow(p,i,q) for i in range(p)]
    # A top-invariant alternating scalar form is determined by one entry per
    # nonzero cyclic difference up to sign. Use coefficient vectors exactly.
    d=(p-1)//2
    def entry(i,j):
        gap=(j-i)%p
        if gap==0:return [0]*d
        if gap>d:return [-x for x in entry(j,i)]
        return [int(k==gap) for k in range(1,d+1)]
    hall=[entry(i,j) for i,j in combinations(range(p),2)
          if (weights[i]+weights[j])%q not in weights]
    physical=[[x-y-z for x,y,z in zip(entry(i,j),entry(i,0),entry(0,j))]
              for i,j in combinations(range(1,p),2)]
    assert rank_mod(physical,p)==d-1
    assert rank_mod(hall+physical,p)==d
    print(p,q,"Hall-permitted scalar dimension",d-rank_mod(hall,p),
          "after physical hyperplane",d-rank_mod(hall+physical,p))
