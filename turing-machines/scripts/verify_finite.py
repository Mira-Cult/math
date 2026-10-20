#!/usr/bin/env python3
"""Independent finite checks for the two exact transition tables.

Uses only the Python standard library and does not import supplied archive code.
This is finite corroboration; Lean sources carry the unbounded proofs.
Run from the repository root: python3 turing-machines/scripts/verify_finite.py
"""
from pathlib import Path
import json, hashlib
ROOT = Path(__file__).resolve().parent.parent
TWELVE = (ROOT / 'machines/collatz12.tm').read_text().strip()
SIXTEEN = (ROOT / 'machines/collatz-cycle16.tm').read_text().strip()
def transition(spec,q,h,t):
 b=int(h in t); row=spec.split('_')[ord(q)-65]; w,d,qq=row[3*b:3*b+3]
 if w=='1': t.add(h)
 else: t.discard(h)
 return qq,h+(1 if d=='R' else -1)
def enc(n,p):
 t=set();i=0
 while n:
  t.add(p+2*i)
  if n%2: t.add(p+2*i+1)
  i+=1;n//=2
 return t
def check12(n,p):
 q='A';h=p;t=enc(n,p);out=n//2 if n%2==0 else (3*n+1)//2
 duration=3 if n==1 else 2 if n%2==0 else 4*out.bit_length()+4
 for j in range(duration):
  assert q!='Z',('early halt',n,j)
  q,h=transition(TWELVE,q,h,t)
 if n==1: assert (q,h,t)==('Z',p+1,set()),(n,q,h,t)
 else: assert (q,h,t)==('A',p+2,enc(out,p+2)),(n,q,h,t,out,duration)
 return duration
def canonical(M,v): return set(range(M))-{v-1}
def check16(M,v):
 q='D';h=0;t=canonical(M,v)
 y=v//2 if v%2==0 else (3*v+1)//2
 if v==1 or y>M: expected=('D',0,canonical(M+1,M+1))
 elif y==M: expected=None
 else: expected=('D',0,canonical(M,y))
 for j in range(1,20*(M+1)**2):
  q,h=transition(SIXTEEN,q,h,t)
  if q=='Z':
   assert expected is None,(M,v,j,'unexpected halt')
   return j
  if q=='D' and h==0:
   assert expected==(q,h,t),(M,v,j,expected,(q,h,t))
   return j
 raise AssertionError(('macro timeout',M,v,q,h,t))
def main():
    steps12=sum(check12(n,(n%11)-5) for n in range(1,65536))
    steps16=sum(check16(M,v) for M in range(2,101) for v in range(1,M+1))
    result={'twelve_cases':65535,'twelve_steps':steps12,'sixteen_cases':sum(range(2,101)),'sixteen_steps':steps16,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result,indent=2))

if __name__ == "__main__":
    main()
