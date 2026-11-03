"""Generate untrusted, kernel-checked text and artifact certificates for the companion.

Lean checks every parsed row, numeric datum, character segment, and the exact
literal binding. The file hash and this producer are provenance only.
"""
from pathlib import Path
from hashlib import sha256
import json

HERE = Path(__file__).resolve().parent
raw = (HERE / 'companion.tm').read_bytes()
if sha256(raw).hexdigest() != '12fba54d7e9c51ca6e149ae4103a3753378a7cff7cfb3e66bcda19804bfeb880':
    raise ValueError('unexpected companion table bytes')
text = raw.decode('ascii')
lines = text.splitlines()
headers = ['#! format beeper-v1', '#! states 286', '#! start 0',
           '#! beep 1', '#! blank 0', '#! head 0']
if lines[:6] != headers or len(lines) != 578 or ('\n'.join(lines)+'\n').encode('ascii') != raw:
    raise ValueError('unexpected header or line structure')
rows = lines[6:]
blocks = [rows[i:i+8] for i in range(0,len(rows),8)]


def lean_chars(text):
    def char(c):
        if c == '\n':
            return "'\\n'"
        if c == "'":
            return "'\\\''"
        if c == '\\':
            return "'\\\\'"
        if not 32 <= ord(c) <= 126:
            raise ValueError('unexpected control character')
        return "'" + c + "'"
    return ','.join(char(c) for c in text)

out = [
    'import Shared.PNP.Record285.CompanionTextSegments', '',
    '/-! Generated, kernel-checked 286-state companion row segments. -/',
    'set_option maxRecDepth 16384', 'set_option maxHeartbeats 0',
    'namespace Shared.PNP.Record285.CompanionTextCertificate',
    'open Shared.PNP.Record285 Shared.PNP.Record285.NumericBinding',
    'open Shared.PNP.Record285.NumericTables Shared.PNP.Record285.CompanionTextSegments',
    'open Shared.PNP.Record285.TextSegments (linesChars clean)',
    'open Shared.Beeping.Machines', '',
]
for i, block in enumerate(blocks):
    parsed, data = [], []
    for line in block:
        state, read, write, direction, target = line.split()
        if direction not in ('L','R'):
            raise ValueError('unexpected direction')
        parsed.append(f'⟨{state},{read},{write},.{"left" if direction == "L" else "right"},{target},0⟩')
        data.append(f'({str(write == "1").lower()},{str(direction == "R").lower()},{target},false)')
    out += [
        f'def lines{i} : List String := ['+','.join(json.dumps(x) for x in block)+']',
        f'def rows{i} : List RawRow := ['+','.join(parsed)+']',
        f'def data{i} : List DataRow := ['+','.join(data)+']',
        f'theorem parsed{i} : lines{i}.mapM (fun s => Companion.parseRow s.toList) = some rows{i} := by decide',
        f'theorem mapped{i} : rows{i}.map companionData = data{i} := by decide',
        f'theorem clean{i} : lines{i}.all clean = true := by decide', '',
    ]
count = len(blocks)
out += [f'def linesFrom{count} : List String := []',
        f'def rowsFrom{count} : List RawRow := []',
        f'def dataFrom{count} : List DataRow := []',
        f'theorem parsedFrom{count} : linesFrom{count}.mapM (fun s => Companion.parseRow s.toList) = some rowsFrom{count} := rfl',
        f'theorem mappedFrom{count} : rowsFrom{count}.map companionData = dataFrom{count} := rfl',
        f'theorem cleanFrom{count} : linesFrom{count}.all clean = true := rfl', '']
for i in range(count-1,-1,-1):
    j=i+1
    out += [
        f'def linesFrom{i} : List String := lines{i} ++ linesFrom{j}',
        f'def rowsFrom{i} : List RawRow := rows{i} ++ rowsFrom{j}',
        f'def dataFrom{i} : List DataRow := data{i} ++ dataFrom{j}',
        f'theorem parsedFrom{i} : linesFrom{i}.mapM (fun s => Companion.parseRow s.toList) = some rowsFrom{i} :=',
        f'  parse_append _ _ _ _ parsed{i} parsedFrom{j}',
        f'theorem mappedFrom{i} : rowsFrom{i}.map companionData = dataFrom{i} := by',
        f'  simp only [rowsFrom{i}, dataFrom{i}, List.map_append, mapped{i}, mappedFrom{j}]',
        f'theorem cleanFrom{i} : linesFrom{i}.all clean = true := by',
        f'  simp only [linesFrom{i}, List.all_append, clean{i}, cleanFrom{j}, Bool.and_self]', '',
    ]
out += [
    'theorem rows_valid : Companion.wellFormed rowsFrom0 = true := by decide', '',
    'theorem numeric_data : rowsFrom0.map companionData = sourceData.toList := by',
    '  rw [mappedFrom0]', '  rfl', '',
    'theorem literal_binding',
    '    (htext : Companion.literal = String.ofList (linesChars (header ++ linesFrom0))) :',
    '    Companion.parse = some rowsFrom0 ∧',
    '      rowsFrom0.map companionData = sourceData.toList :=',
    '  ⟨parse_of_lines linesFrom0 rowsFrom0 cleanFrom0 parsedFrom0 htext, numeric_data⟩', '',
    'end Shared.PNP.Record285.CompanionTextCertificate',
]
(HERE / 'CompanionTextCertificate.lean').write_text('\n'.join(out)+'\n',encoding='utf-8')

out = [
    'import Shared.PNP.Record285.CompanionTextCertificate',
    'import Shared.PNP.Record285.ArtifactCertificate', '',
    '/-! Kernel-checked exact literal-to-segment binding for the companion. -/',
    'set_option maxRecDepth 131072', 'set_option maxHeartbeats 0',
    'namespace Shared.PNP.Record285.CompanionArtifactCertificate',
    'open Shared.PNP.Record285 Shared.PNP.Record285.CompanionTextCertificate',
    'open Shared.PNP.Record285.CompanionTextSegments',
    'open Shared.PNP.Record285.TextSegments (linesChars)',
    'open Shared.PNP.Record285.ArtifactCertificate (lines_append)', '',
    'def literalChars : List Char := ['+lean_chars(text)+']',
    'theorem literal_chars : Companion.literal = String.ofList literalChars := by rfl', '',
    'def headerChars : List Char := ['+lean_chars('\n'.join(headers)+'\n')+']',
    'theorem header_chars : linesChars header = headerChars := by decide', '',
]
for i, block in enumerate(blocks):
    out += [f'def chars{i} : List Char := ['+lean_chars('\n'.join(block)+'\n')+']',
            f'theorem chars_ok{i} : linesChars lines{i} = chars{i} := by decide', '']
out += [f'def charsFrom{count} : List Char := []',
        f'theorem charsFrom_ok{count} : linesChars linesFrom{count} = charsFrom{count} := rfl', '']
for i in range(count-1,-1,-1):
    j=i+1
    out += [f'def charsFrom{i} : List Char := chars{i} ++ charsFrom{j}',
            f'theorem charsFrom_ok{i} : linesChars linesFrom{i} = charsFrom{i} := by',
            f'  change linesChars (lines{i} ++ linesFrom{j}) = chars{i} ++ charsFrom{j}',
            f'  rw [lines_append, chars_ok{i}, charsFrom_ok{j}]', '']
out += [
    'theorem chars_concat : literalChars = headerChars ++ charsFrom0 := by rfl', '',
    'theorem artifactMatches :',
    '    Companion.literal = String.ofList (linesChars (header ++ linesFrom0)) := by',
    '  rw [literal_chars, lines_append, header_chars, charsFrom_ok0, chars_concat]', '',
    'end Shared.PNP.Record285.CompanionArtifactCertificate',
]
(HERE / 'CompanionArtifactCertificate.lean').write_text('\n'.join(out)+'\n',encoding='utf-8')
print(f'{len(rows)} rows, {len(blocks)} segments, {len(text)} characters')
