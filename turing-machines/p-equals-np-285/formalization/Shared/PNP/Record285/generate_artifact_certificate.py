"""Generate a kernel-checked exact text-to-segments certificate.

The producer reads the frozen file but is untrusted: Lean checks both the
literal-to-character-list equality and every segment concatenation. Run from
any directory with Python 3.11+.
"""
from pathlib import Path
from hashlib import sha256

HERE = Path(__file__).resolve().parent
raw = (HERE / 'events.tm').read_bytes()
if sha256(raw).hexdigest() != '1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7':
    raise ValueError('unexpected event table bytes')
text = raw.decode('ascii')
lines = text.splitlines()
if ('\n'.join(lines) + '\n').encode('ascii') != raw or len(lines) != 575:
    raise ValueError('unexpected line structure')


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

blocks = [lines[i:i+8] for i in range(5, len(lines), 8)]
out = [
    'import Shared.PNP.Record285.TextEndpoint', '',
    '/-! Generated exact literal-to-segment binding. The literal equality is',
    'checked by the kernel; the generator is not trusted. -/',
    'set_option maxRecDepth 131072', 'set_option maxHeartbeats 0',
    'namespace Shared.PNP.Record285.ArtifactCertificate',
    'open Shared.PNP.Record285 Shared.PNP.Record285.TextEndpoint',
    'open Shared.PNP.Record285.TextSegments Shared.PNP.Record285.TextCertificate', '',
    'theorem lines_append (a b : List String) :',
    '    linesChars (a ++ b) = linesChars a ++ linesChars b := by',
    '  induction a with',
    '  | nil => rfl',
    '  | cons a as ih => simp [linesChars, ih, List.append_assoc]', '',
    'def literalChars : List Char := [' + lean_chars(text) + ']',
    '/-- The literal is definitionally the exact character list. -/',
    'theorem literal_chars : literal = String.ofList literalChars := by rfl', '',
    'def headerChars : List Char := [' + lean_chars('\n'.join(lines[:5])+'\n') + ']',
    'theorem header_chars : linesChars header = headerChars := by decide', '',
]
for i, block in enumerate(blocks):
    out += [f'def chars{i} : List Char := [' + lean_chars('\n'.join(block)+'\n') + ']',
            f'theorem chars_ok{i} : linesChars lines{i} = chars{i} := by decide', '']
count = len(blocks)
out += [f'def charsFrom{count} : List Char := []',
        f'theorem charsFrom_ok{count} : linesChars linesFrom{count} = charsFrom{count} := rfl', '']
for i in range(count-1, -1, -1):
    j = i+1
    out += [f'def charsFrom{i} : List Char := chars{i} ++ charsFrom{j}',
            f'theorem charsFrom_ok{i} : linesChars linesFrom{i} = charsFrom{i} := by',
            f'  change linesChars (lines{i} ++ linesFrom{j}) = chars{i} ++ charsFrom{j}',
            f'  rw [lines_append, chars_ok{i}, charsFrom_ok{j}]', '']
out += [
    'theorem chars_concat : literalChars = headerChars ++ charsFrom0 := by rfl', '',
    '/-- The embedded artifact equals the checked segments, with no premise. -/',
    'theorem artifactMatches : ArtifactMatches := by',
    '  unfold ArtifactMatches',
    '  rw [literal_chars, lines_append, header_chars, charsFrom_ok0, chars_concat]', '',
    'end Shared.PNP.Record285.ArtifactCertificate',
]
(HERE / 'ArtifactCertificate.lean').write_text('\n'.join(out)+'\n', encoding='utf-8')
print(f'{len(text)} characters, {len(blocks)} row segments')
