#!/usr/bin/env python3
"""Generate the untrusted FT odd-base list and its order proof input."""
from pathlib import Path
from math import isqrt
B=32768
flags=bytearray([1])*(B+1)
flags[:2]=b'\x00\x00'
for p in range(2,isqrt(B)+1):
    if flags[p]:
        for j in range(p*p,B+1,p): flags[j]=0
primes=[i for i in range(3,B+1,2) if flags[i]]
lines=[', '.join(map(str,primes[i:i+20])) for i in range(0,len(primes),20)]
Path('Sude/FiniteTwinOddBaseData.lean').write_text('''import Sude.StreamingPrefix16384

namespace Sude
noncomputable section

def finiteTwinOddBase : List ℕ := [\n  '''+',\n  '.join(lines)+'''\n]

end
end Sude
''')
Path('Sude/FiniteTwinOddBaseOrder.lean').write_text('''import Sude.FiniteTwinOddBaseData
import Mathlib.Data.List.Sort

namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem finiteTwinOddBase_sorted : finiteTwinOddBase.SortedLT := by
  decide +kernel

theorem finiteTwinOddBase_length : finiteTwinOddBase.length = 3511 := by
  decide +kernel

end
end Sude
''')
print(len(primes))
