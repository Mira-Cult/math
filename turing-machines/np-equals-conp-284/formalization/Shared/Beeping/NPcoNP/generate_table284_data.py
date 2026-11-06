"""Translate the pinned ASCII table into Lean raw data (not a proof of parsing)."""
from pathlib import Path

source = Path('Shared/Beeping/NPcoNP/Inputs/selected284-events.tm')
output = Path('Shared/Beeping/NPcoNP/Table284Data.lean')
lines = source.read_text(encoding='ascii').splitlines()
assert lines[:5] == ['#! format beeper-events-v1', '#! states 284',
                     '#! start 0', '#! blank 0', '#! head 0']
assert len(lines) == 5 + 568
rows = {}
for line in lines[5:]:
    fields = line.split()
    assert len(fields) == 6
    q, read, write, move, dest, beep = fields
    assert q.isascii() and q.isdecimal() and dest.isascii() and dest.isdecimal()
    q, dest = int(q), int(dest)
    assert q < 284 and dest < 284 and read in ('0', '1')
    assert write in ('0', '1') and move in ('L', 'R') and beep in ('0', '1')
    key = (q, int(read))
    assert key not in rows
    rows[key] = (write == '1', move == 'R', dest, beep == '1')
assert set(rows) == {(q, b) for q in range(284) for b in range(2)}
def boolean(b):
    return 'true' if b else 'false'
def row(item):
    w, m, d, b = item
    return f'({boolean(w)}, ({boolean(m)}, ({d}, {boolean(b)})))'
result = [
    'import Shared.Beeping.TableBits', '',
    '/-! Generated numeric representation. The ASCII parser binding is not yet',
    'kernel proved; see generate_table284_data.py and Inputs/selected284-events.tm. -/',
    'namespace Shared.Beeping.NPcoNP.Table284',
    'open Shared.Beeping.TableBits', '',
    'def data : RawMachine := ((0, (false, 0)), [',
]
for q in range(284):
    suffix = ',' if q < 283 else ''
    result.append(f'  ({row(rows[(q, 0)])}, {row(rows[(q, 1)])}){suffix}')
result.extend(['])', '', 'end Shared.Beeping.NPcoNP.Table284', ''])
output.write_text('\n'.join(result), encoding='utf-8')
