#!/usr/bin/env python3
"""Untrusted reproducible producer of the M236 packed runtime certificate.

Every generated check is replayed by Lean against a proved lookup of raw.tm.
The generator is not a source of mathematical correctness.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RAW = ROOT / 'bindings/m236/raw.tm'
LEAN = ROOT / 'lean/PASoundness'
RAW_SHA256 = 'e73b3c7fbcbbc4614e4ee33a6e33cacfb3b8e2dc32822591db2afdfedf01a9e8'
CHUNK = 1000
PER_PART = 5

def inputs():
    raw = RAW.read_bytes()
    if hashlib.sha256(raw).hexdigest() != RAW_SHA256:
        raise ValueError('raw table does not match the pinned M236 input')
    rows = {}
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#'):
            continue
        q, read, write, direction, dest, event = line.split()
        q, read, write, dest = map(int, (q, read, write, dest))
        if (q, read) in rows or direction not in ('L', 'R') or event not in ('-', '0', '1'):
            raise ValueError('malformed row')
        rows[q, read] = (write, direction, dest, event)
    if set(rows) != {(q, b) for q in range(237) for b in (0, 1)}:
        raise ValueError('raw table is not complete')
    return rows

def bit(b):
    return 'true' if b else 'false'

def fast_table(rows):
    def row(q, read):
        w, d, dest, _ = rows[q, read]
        return f'⟨{bit(w)}, .{"right" if d == "R" else "left"}, {dest}, false⟩'
    def tree(lo, hi):
        if hi - lo == 1:
            return f'(if read then {row(lo, 1)} else {row(lo, 0)})'
        mid = (lo + hi) // 2
        return f'(if q.val < {mid} then {tree(lo, mid)} else {tree(mid, hi)})'
    s = '''import PASoundness.M236PackedFast

/-! Generated lookup for the pinned raw table. The two exhaustive checks below
prove every transition and event label equal to the canonical Lean table. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PASoundness.M236.FastTable
open Shared.Beeping.Machines PASoundness.M236.PackedFast
'''
    s += 'def row (q : Fin 237) (read : Bool) : Row 237 :=\n  ' + tree(0, 237) + '\n'
    s += 'def event (q : Fin 237) (read : Bool) : Option Bool :=\n'
    for (q, b), (_, _, _, e) in sorted(rows.items()):
        if e != '-':
            s += f'  if q.val = {q} ∧ read = {bit(b)} then some {bit(int(e))} else\n'
    s += '''  none

def table : Lookup 237 := ⟨row, event⟩

theorem rows_correct : ∀ (q : Fin 237) (b : Bool), row q b = raw.table.row q b := by decide

theorem events_correct : ∀ (q : Fin 237) (b : Bool), event q b = rawLabels.at q b := by decide

theorem table_correct : table = ordinary raw rawLabels := by
  have hr : row = raw.table.row := funext fun q => funext fun b => rows_correct q b
  have he : event = rawLabels.at := funext fun q => funext fun b => events_correct q b
  simp [table, ordinary, hr, he]
end PASoundness.M236.FastTable
'''
    return s

def pop(cs):
    while cs:
        x = cs.pop(0)
        if x[0] == 'b':
            return x[1]
        _, a, b, n = x
        if n:
            cs.insert(0, ('p', a, b, n - 1))
            cs.insert(0, ('b', b))
            return a
    return 0

def push_pairs(a, b, n, cs):
    if not n:
        return
    if cs and cs[0][0] == 'p' and cs[0][1:3] == (a, b):
        n += cs.pop(0)[3]
    cs.insert(0, ('p', a, b, n))

def push_bit(b, cs):
    if cs and cs[0][0] == 'b':
        push_pairs(b, cs.pop(0)[1], 1, cs)
    else:
        cs.insert(0, ('b', b))

def peek(cs):
    for x in cs:
        if x[0] == 'b':
            return x[1], True
        if x[3]:
            return x[1], True
    return 0, False

def collect(rows):
    q, head, ticks = 58, -2, 0
    left = [('p', 1, 0, 1909), ('b', 1)]
    right = [('b', b) for b in (1, 0, 1, 1, 1, 1)]
    def state():
        return (q, head, tuple(left), tuple(right))
    first = state()
    start_tick = 0
    ops = []
    chunks = []
    while ticks < 89821408 - 2133492:
        if q == 79:
            raise ValueError('runtime reached too early')
        chosen = None
        if right and right[0][0] == 'p':
            _, a, b, n = right[0]
            w, d, target, e = rows[q, a]
            v, d2, target2, e2 = rows[target, b]
            if n and d == d2 == 'R' and target2 == q and e == e2 == '-':
                right.pop(0)
                right.insert(0, ('p', a, b, 0))
                push_pairs(v, w, n, left)
                head += 2 * n
                ticks += 2 * n
                chosen = ('r', n)
        if chosen is None and left and left[0][0] == 'p':
            _, b, a, n = left[0]
            symbol, present = peek(right)
            w, d, target, e = rows[q, a]
            v, d2, target2, e2 = rows[target, b]
            if n and present and symbol == a and d == d2 == 'L' and target2 == q and e == e2 == '-':
                left.pop(0)
                left.insert(0, ('p', b, a, 0))
                pop(right)
                push_pairs(v, w, n, right)
                push_bit(a, right)
                head -= 2 * n
                ticks += 2 * n
                chosen = ('l', n)
        if chosen is None:
            symbol = pop(right)
            w, d, q, e = rows[q, symbol]
            if e != '-':
                raise ValueError('unexpected initializer event')
            if d == 'R':
                push_bit(w, left)
                head += 1
            else:
                new_head = pop(left)
                push_bit(w, right)
                push_bit(new_head, right)
                head -= 1
            ticks += 1
            chosen = ('1', 0)
        ops.append(chosen)
        if len(ops) == CHUNK:
            chunks.append((first, tuple(ops), state(), ticks - start_tick))
            first, start_tick, ops = state(), ticks, []
    if ops:
        chunks.append((first, tuple(ops), state(), ticks - start_tick))
    if (q, head, ticks) != (79, -3818, 89821408 - 2133492):
        raise ValueError('unexpected runtime-entry candidate')
    return chunks

def chunk_text(c):
    if c[0] == 'b':
        return '.bit ' + bit(c[1])
    return f'.pair {bit(c[1])} {bit(c[2])} {c[3]}'

def state_text(s):
    q, h, left, right = s
    l = ', '.join(map(chunk_text, left))
    r = ', '.join(map(chunk_text, right))
    return f'⟨{q}, {h}, ⟨[{l}], [{r}]⟩⟩'

def op_text(op):
    k, n = op
    return '.one' if k == '1' else f'.{"right" if k == "r" else "left"} {n}'

def part_text(part, chunks):
    name = f'Part{part:02d}'
    s = f'''import PASoundness.M236RuntimeBase

/-! Generated, untrusted operation and checkpoint data; all checks are kernel reduced. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PASoundness.M236.RuntimeCertificate.{name}
open PASoundness.M236.PackedTape PASoundness.M236.RuntimeBase
open PASoundness.M236.FastBootstrap
'''
    s += f'def state0 : Configuration 237 := {"start" if part == 0 else state_text(chunks[0][0])}\n'
    for i, (_, ops, end, ticks) in enumerate(chunks):
        s += f'def ops{i} : List PackedTape.Op := [' + ', '.join(map(op_text, ops)) + ']\n'
        s += f'def state{i+1} : Configuration 237 := {state_text(end)}\n'
        s += f'def ticks{i} : Nat := {ticks}\n'
        s += f'theorem check{i} : PackedFast.run FastTable.table state{i} ops{i} = some (state{i+1}, ticks{i}, []) := by decide\n'
    s += '\n/-- Exact silent segment for these checked operations. -/\n'
    s += f'theorem block : rawSystem.Block (unpackConfig state0) {sum(c[3] for c in chunks)} (unpackConfig state{len(chunks)}) [] := by\n'
    for i in range(len(chunks)):
        s += f'  have b{i} := (segment_sound ops{i} state{i} state{i+1} ticks{i} [] check{i}).1\n'
        if i:
            s += f'  have all{i} := {"b0" if i == 1 else f"all{i-1}"}.trans rawSystem b{i}\n'
    final = 'b0' if len(chunks) == 1 else f'all{len(chunks)-1}'
    s += '  simpa [' + ', '.join(f'ticks{i}' for i in range(len(chunks))) + f'] using {final}\n'
    return s + f'end PASoundness.M236.RuntimeCertificate.{name}\n'

def generate(rows, chunks):
    out = {LEAN / 'M236FastTable.lean': fast_table(rows)}
    count = (len(chunks) + PER_PART - 1) // PER_PART
    for p in range(count):
        selected = chunks[p*PER_PART:(p+1)*PER_PART]
        out[LEAN / f'M236RuntimePart{p:02d}.lean'] = part_text(p, selected)
    imports = ''.join(f'import PASoundness.M236RuntimePart{p:02d}\n' for p in range(count))
    last_count = len(chunks) - PER_PART * (count - 1)
    last = f'Part{count-1:02d}.state{last_count}'
    s = imports + '''
/-! Generated composition of all kernel-checked packed initializer segments. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.RuntimeCertificate
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.PackedTape
open PASoundness.M236.FastBootstrap PASoundness.M236.FastBootstrap.Certificate
'''
    s += f'''/-- Exact raw execution from the completely blank tape through runtime entry. -/
theorem raw_block : rawSystem.Block rawSystem.initial 89821408 (unpackConfig {last}) [] := by
'''
    for p in range(count):
        s += f'  have b{p} := Part{p:02d}.block\n'
        if p:
            s += f'  have all{p} := {"b0" if p == 1 else f"all{p-1}"}.trans rawSystem b{p}\n'
    final = 'b0' if count == 1 else f'all{count-1}'
    s += f'''  change rawSystem.Block (unpackConfig RuntimeBase.start) _ _ [] at {final}
  rw [RuntimeBase.start_unpacked] at {final}
  have h := bootstrap_block.trans rawSystem {final}
  simpa using h

/-- Full two-way raw tape and event prefix at runtime entry. -/
theorem raw_entry :
    Related (unpackConfig {last}) ((machineWordSystem raw rawLabels).run 89821408) ∧
      (machineWordSystem raw rawLabels).prefixWord 89821408 = [] := by
  have h := raw_run_sound 89821408
  change Related (rawSystem.advance rawSystem.initial 89821408) _ ∧
    rawSystem.wordFrom rawSystem.initial 89821408 = _ at h
  rw [raw_block.endpoint, raw_block.output] at h
  exact ⟨h.1, h.2.symm⟩

/-- The selected quotient reaches state 78 at head −3818 with exactly the
same complete tape and no preceding output bits. -/
theorem selected_entry :
    Related ⟨78, -3818, (unpackConfig {last}).tape⟩
      ((machineWordSystem machine machineLabels).run 89821408) ∧
      (machineWordSystem machine machineLabels).prefixWord 89821408 = [] := by
  have hrel := related_map raw_entry.1
  rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels] at hrel
  have hm : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, -3818, (unpackConfig {last}).tape⟩ _ at hrel
  rw [hm] at hrel
  exact ⟨hrel, by rw [← prefix_eq]; exact raw_entry.2⟩

end PASoundness.M236.RuntimeCertificate
'''
    out[LEAN / 'M236RuntimeCertificate.lean'] = s
    return out

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    rows = inputs()
    chunks = collect(rows)
    out = generate(rows, chunks)
    for path, text in out.items():
        if args.check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f'generated source differs: {path}')
        elif not path.exists() or path.read_text() != text:
            path.write_text(text)
    print(f'{len(chunks)} chunks, {sum(len(x[1]) for x in chunks)} operations, {sum(x[3] for x in chunks)} candidate transitions')

if __name__ == '__main__':
    main()
