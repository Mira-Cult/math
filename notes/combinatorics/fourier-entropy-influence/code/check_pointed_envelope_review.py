#!/usr/bin/env python3
"""Independent certified small checks for Section 9's generic leaf envelope.
Uses only the rational log-interval implementation in the reviewed checker;
constructs all Boolean truth tables and aligned scores independently.
"""
from fractions import Fraction as Q
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
p=Path(__file__).with_name('check_recursive_point_interference.py')
s=spec_from_file_location('certified_logs',p);m=module_from_spec(s);s.loader.exec_module(m)
count=0
for n in (2,3):
 size=1<<n
 for truth in range(1<<size):
  values=[1-2*((truth>>x)&1) for x in range(size)]
  w=m.walsh(values)
  if any(v==0 for v in w):continue
  influence=Q(m.edge_count(values,n),size)
  assert n*Q(2,size)<=influence
  elow,ehigh=m.linear_log_interval([(abs(v),Q(2*v*v,size*size)) for v in w])
  Hlow,Hhigh=2*n-ehigh,2*n-elow
  assert Hhigh<=4*influence
  for x in range(size):
   aligned=[values[x]*(-1)**((s&x).bit_count()%2)*v for s,v in enumerate(w)]
   blow,bhigh=m.linear_log_interval([(abs(v),Q(2*(v-1),size)) for v in aligned])
   delta=Q(2,size)
   assert delta*max(abs(blow),abs(bhigh))<=16*influence
   sensitivity=sum(values[x]!=values[x^(1<<i)] for i in range(n));t=n-2*sensitivity
   C=Q(23);ulo,uhi=2*blow-C*t,2*bhigh-C*t
   margin=C*influence-Hhigh
   assert margin>=delta*(Q(4,7)+max(abs(ulo),abs(uhi))/3)
   count+=1
print('PASS exact rational intervals:',count,'pointed positive-spectrum Boolean leaves, n=2,3')
print('PASS C0=4 to C=23 leaf invariant; score bound16 and n delta <=I')
