#!/usr/bin/env python3
"""Generate untrusted text chunks for Lean's exact M236 graph binding."""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
raw = (root / 'bindings/m236/occurrence-graph.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != 'dbad7675ad75b28ff70f26387f0cb6cbeabe5dea586d681eefa47c11c422ae93':
    raise ValueError('unexpected pinned occurrence graph')
data = json.loads(raw)
if len(data) != 760:
    raise ValueError('expected 760 graph rows')
parts = [[json.dumps(row, separators=(',', ':')) for row in data[i:i+95]]
         for i in range(0, 760, 95)]
base = '''import PASoundness.M236OccurrenceGraphData
/-! File-specific serializer for the retained occurrence graph. -/
namespace PASoundness.M236.OccurrenceGraph.Text
open PASoundness.M236.OccurrenceGraph

def rowText (row : String × Nat × Option Nat) : String :=
  let (name, dest, extra) := row
  "[\\\"" ++ name ++ "\\\"," ++ toString dest ++
    (match extra with | none => "" | some target => "," ++ toString target) ++ "]"

def groupText (rows : Array (String × Nat × Option Nat)) (i : Nat) : String :=
  String.intercalate "," (((rows.toList.drop (95 * i)).take 95).map rowText)

def serialize (rows : Array (String × Nat × Option Nat)) : String :=
  "[" ++ ''' + ' ++ "," ++ '.join(f'groupText rows {i}' for i in range(8)) + ''' ++ "]\\n"
end PASoundness.M236.OccurrenceGraph.Text
'''
outputs = {'M236OccurrenceGraphTextFormat.lean': base}
for i, part in enumerate(parts):
    outputs[f'M236OccurrenceGraphTextPart{i}.lean'] = '\n'.join([
        'import PASoundness.M236OccurrenceGraphTextFormat',
        'set_option maxRecDepth 524288', 'set_option maxHeartbeats 0',
        'namespace PASoundness.M236.OccurrenceGraph.Text',
        'open PASoundness.M236.OccurrenceGraph',
        f'def part{i} : List String := {json.dumps(part, ensure_ascii=True)}',
        f'theorem part{i}_checked : part{i} = (((sourceRows.toList.drop (95 * {i})).take 95).map rowText) := by decide',
        f'theorem group{i}_checked : String.intercalate "," part{i} = groupText sourceRows {i} :=',
        f'  congrArg (String.intercalate ",") part{i}_checked',
        'end PASoundness.M236.OccurrenceGraph.Text', ''])
part_list = ' ++ '.join(f'part{i}' for i in range(8))
group_list = ' ++ '.join(f'groupRows rows {i}' for i in range(8))
main = ['import PASoundness.M236Ascii',
        *(f'import PASoundness.M236OccurrenceGraphTextPart{i}' for i in range(8)),
        '/-! Exact file-specific byte binding for the retained graph.',
        'Generated witnesses are untrusted; Lean checks every comparison. -/',
        'set_option maxRecDepth 524288', 'set_option maxHeartbeats 0',
        'namespace PASoundness.M236.OccurrenceGraph.Text',
        'open PASoundness.M236.OccurrenceGraph PASoundness.M236.TextEncoding',
        'def fileBytes : List UInt8 := [' + ', '.join(map(str, raw)) + ']',
        'def groupRows (rows : Array (String × Nat × Option Nat)) (i : Nat) : List String :=',
        '  (((rows.toList.drop (95 * i)).take 95).map rowText)',
        'def serializeBytes (rows : Array (String × Nat × Option Nat)) : List UInt8 :=',
        '  [91] ++ List.intercalate [44] ((' + group_list + ').map bytes) ++ [93, 10]',
        'def input : String := include_str ".." / ".." / "bindings" / "m236" / "occurrence-graph.json"',
        'theorem input_chars : input = String.ofList (fileBytes.map fun b => Char.ofNat b.toNat) := by rfl',
        'theorem ascii_checked : fileBytes.all (fun b => decide (b.toNat < 128)) = true := by decide',
        'theorem input_checked : input.toByteArray = ⟨⟨fileBytes⟩⟩ := by',
        '  rw [input_chars, String.toByteArray_ofList]',
        '  apply PASoundness.M236.Ascii.encode_list',
        '  intro b hb',
        '  exact of_decide_eq_true ((List.all_eq_true.mp ascii_checked) b hb)',
        'theorem assembled : fileBytes = [91] ++ List.intercalate [44] ((' + part_list + ').map bytes) ++ [93, 10] := by decide',
        '/-- Exact file bytes equal serialization of the Lean graph.',
        'Rebuild after modifying the included file. -/',
        'theorem binding : bytes input = serializeBytes sourceRows := by',
        '  unfold bytes',
        '  rw [input_checked]',
        '  change fileBytes = _',
        '  rw [assembled, ' + ', '.join(f'part{i}_checked' for i in range(8)) + ']',
        '  rfl',
        'end PASoundness.M236.OccurrenceGraph.Text', '']
outputs['M236OccurrenceGraphText.lean'] = '\n'.join(main)
for name, result in outputs.items():
    output = root / 'lean/PASoundness' / name
    if '--check' in sys.argv:
        if not output.exists() or output.read_text() != result:
            raise SystemExit(f'M236 graph text witness differs: {name}')
    else:
        output.write_text(result)
if '--check' in sys.argv:
    print('M236 graph text witnesses match retained graph')
