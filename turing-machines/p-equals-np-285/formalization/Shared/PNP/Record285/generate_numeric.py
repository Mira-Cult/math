"""Generate the untrusted numeric copies used by the quotient certificate.

The Lean checker proves the numeric quotient. This generator's validation and
hashes do not prove equality between the numeric copies and the text parsers.
Run from any directory with Python 3.11+.
"""
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent


def entries(name, digest, states, event_column):
    raw = (HERE / name).read_bytes()
    if sha256(raw).hexdigest() != digest:
        raise ValueError(f'unexpected bytes: {name}')
    rows = [line.split() for line in raw.decode('ascii').splitlines() if not line.startswith('#')]
    if len(rows) != 2 * states:
        raise ValueError(f'wrong row count: {name}')
    result = []
    for index, row in enumerate(rows):
        if len(row) != (6 if event_column else 5):
            raise ValueError(f'wrong row width: {name}:{index}')
        state, read, write, direction, target = row[:5]
        event = row[5] if event_column else '0'
        if (int(state) != index // 2 or int(read) != index % 2 or write not in ('0', '1')
                or direction not in ('L', 'R') or not 0 <= int(target) < states
                or event not in ('0', '1')):
            raise ValueError(f'invalid row: {name}:{index}')
        result.append('(' + ','.join(('true' if write == '1' else 'false',
                                      'true' if direction == 'R' else 'false', target,
                                      'true' if event == '1' else 'false')) + ')')
    return ',\n'.join(result)

source = entries('companion.tm', '12fba54d7e9c51ca6e149ae4103a3753378a7cff7cfb3e66bcda19804bfeb880', 286, False)
target = entries('events.tm', '1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7', 285, True)
text = '''import Shared.Beeping.Machines

/-! Generated numeric copies of the two frozen tables. The separate proof
checks their quotient. Equality with the text-parsed machines remains open. -/
namespace Shared.PNP.Record285.NumericTables
open Shared.Beeping.Machines
abbrev DataRow := Bool × Bool × Nat × Bool
'''
text += 'def sourceData : Array DataRow := #[\n' + source + '\n]\n'
text += 'def targetData : Array DataRow := #[\n' + target + '\n]\n'
text += '''
def numericRow {n : Nat} (hn : 0 < n) (v : DataRow) : Row n :=
  ⟨v.1, if v.2.1 then .right else .left, ⟨v.2.2.1 % n, Nat.mod_lt _ hn⟩, v.2.2.2⟩

def numericTable (n : Nat) (hn : 0 < n) (data : Array DataRow) : Table n :=
  ⟨Vector.ofFn fun q =>
    (numericRow hn (data[2*q.val]?.getD (false,false,0,false)),
     numericRow hn (data[2*q.val+1]?.getD (false,false,0,false)))⟩

def source : Machine 286 := ⟨numericTable 286 (by decide) sourceData, ⟨0,by decide⟩, false, 0⟩
def target : Machine 285 := ⟨numericTable 285 (by decide) targetData, ⟨0,by decide⟩, false, 0⟩
end Shared.PNP.Record285.NumericTables
'''
(HERE / 'NumericTables.lean').write_text(text, encoding='utf-8')
