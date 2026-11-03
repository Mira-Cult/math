"""Generate untrusted, kernel-checkable row chunks from the frozen table.

The Lean proofs check every parsed row and its numeric data. The separate exact
file-to-lines equality is a theorem premise, not established by this generator
or its hash test. Run with Python 3.11+.
"""
from hashlib import sha256
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
EXPECTED_HASH = '1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7'
raw = (HERE / 'events.tm').read_bytes()
if sha256(raw).hexdigest() != EXPECTED_HASH:
    raise ValueError('unexpected event table bytes')
lines = raw.decode('ascii').splitlines()
if lines[:5] != ['#! format beeper-events-v1', '#! states 285', '#! start 0',
                 '#! blank 0', '#! head 0'] or len(lines) != 575 or not raw.endswith(b'\n'):
    raise ValueError('unexpected header, row count, or final newline')
if ('\n'.join(lines) + '\n').encode('ascii') != raw:
    raise ValueError('text does not round-trip exactly')
rows = lines[5:]
blocks = [rows[i:i+8] for i in range(0, len(rows), 8)]
out = [
    'import Shared.PNP.Record285.TextSegments', '',
    '/-! Generated row segments. Each segment is parsed and compared with',
    'the numeric data by kernel reduction. Equality with the embedded source',
    'file is a separate explicit premise in `literal_binding`. -/',
    'set_option maxRecDepth 16384', 'set_option maxHeartbeats 0',
    'namespace Shared.PNP.Record285.TextCertificate',
    'open Shared.PNP.Record285 Shared.PNP.Record285.NumericBinding',
    'open Shared.PNP.Record285.NumericTables Shared.PNP.Record285.TextSegments',
    'open Shared.Beeping.Machines', '',
]
for i, block in enumerate(blocks):
    parsed, data = [], []
    for line in block:
        state, read, write, direction, target, event = line.split()
        if direction not in ('L', 'R'):
            raise ValueError('unexpected direction')
        parsed.append(f'⟨{state},{read},{write},.{"left" if direction == "L" else "right"},{target},{event}⟩')
        data.append(f'({str(write == "1").lower()},{str(direction == "R").lower()},'
                    f'{target},{str(event == "1").lower()})')
    out += [
        f'def lines{i} : List String := [' + ','.join(json.dumps(x) for x in block) + ']',
        f'def rows{i} : List RawRow := [' + ','.join(parsed) + ']',
        f'def data{i} : List DataRow := [' + ','.join(data) + ']',
        f'theorem parsed{i} : lines{i}.mapM (fun s => parseRow s.toList) = some rows{i} := by decide',
        f'theorem mapped{i} : rows{i}.map markedData = data{i} := by decide',
        f'theorem clean{i} : lines{i}.all clean = true := by decide', '',
    ]
count = len(blocks)
out += [f'def linesFrom{count} : List String := []',
        f'def rowsFrom{count} : List RawRow := []',
        f'def dataFrom{count} : List DataRow := []',
        f'theorem parsedFrom{count} : linesFrom{count}.mapM (fun s => parseRow s.toList) = some rowsFrom{count} := rfl',
        f'theorem mappedFrom{count} : rowsFrom{count}.map markedData = dataFrom{count} := rfl',
        f'theorem cleanFrom{count} : linesFrom{count}.all clean = true := rfl', '']
for i in range(count-1, -1, -1):
    j = i+1
    out += [
        f'def linesFrom{i} : List String := lines{i} ++ linesFrom{j}',
        f'def rowsFrom{i} : List RawRow := rows{i} ++ rowsFrom{j}',
        f'def dataFrom{i} : List DataRow := data{i} ++ dataFrom{j}',
        f'theorem parsedFrom{i} : linesFrom{i}.mapM (fun s => parseRow s.toList) = some rowsFrom{i} :=',
        f'  parse_append _ _ _ _ parsed{i} parsedFrom{j}',
        f'theorem mappedFrom{i} : rowsFrom{i}.map markedData = dataFrom{i} := by',
        f'  simp only [rowsFrom{i}, dataFrom{i}, List.map_append, mapped{i}, mappedFrom{j}]',
        f'theorem cleanFrom{i} : linesFrom{i}.all clean = true := by',
        f'  simp only [linesFrom{i}, List.all_append, clean{i}, cleanFrom{j}, Bool.and_self]', '',
    ]
out += [
    '/-- The segmented rows satisfy ordering, bounds and the single-event mask. -/',
    'theorem rows_valid : wellFormed rowsFrom0 = true := by decide', '',
    '/-- Numeric arrays and the concatenated row data agree exactly. -/',
    'theorem numeric_data : rowsFrom0.map markedData = targetData.toList := by',
    '  rw [mappedFrom0]',
    '  rfl', '',
    '/-- The only outstanding premise is equality of the embedded file with',
    'these checked text lines. This is not proved by the generator hash. -/',
    'theorem literal_binding',
    '    (htext : literal = String.ofList (linesChars (header ++ linesFrom0))) :',
    '    Shared.PNP.Record285.parse = some rowsFrom0 ∧',
    '      rowsFrom0.map markedData = targetData.toList :=',
    '  ⟨parse_of_lines linesFrom0 rowsFrom0 cleanFrom0 parsedFrom0 htext, numeric_data⟩', '',
    'end Shared.PNP.Record285.TextCertificate',
]
(HERE / 'TextCertificate.lean').write_text('\n'.join(out) + '\n', encoding='utf-8')
print(f'{len(rows)} rows, {count} checked text segments')
