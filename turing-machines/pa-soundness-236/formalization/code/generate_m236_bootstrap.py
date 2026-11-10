#!/usr/bin/env python3
"""Generate a checked, chunked M236 bootstrap certificate from pinned rows.

The simulator is untrusted. Every generated chunk is checked in Lean by
`runOps`; `perform_sound` and `blank_program_sound` supply the soundness
argument. The output is source proof input, not a raw execution log.
"""

from collections import deque
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
MACHINE = ROOT / "bindings" / "m236" / "raw.tm"
LEAN = ROOT / "lean" / "PASoundness"
SHA256 = "e73b3c7fbcbbc4614e4ee33a6e33cacfb3b8e2dc32822591db2afdfedf01a9e8"
CHUNK_SIZE = 100
PART_SIZE = 10


def load_rows():
    data = MACHINE.read_bytes()
    if hashlib.sha256(data).hexdigest() != SHA256:
        raise ValueError("raw machine bytes differ from the pinned input")
    lines = data.decode("ascii").splitlines()
    if lines[:5] != ["#! format bit-events-v1", "#! states 237", "#! start 0",
                     "#! blank 0", "#! head 0"]:
        raise ValueError("unexpected header")
    rows = {}
    for index, line in enumerate(lines[5:]):
        q, read, write, direction, target, event = line.split()
        if int(q) != index // 2 or int(read) != index % 2:
            raise ValueError("unexpected row order")
        rows[int(q), int(read)] = int(write), direction, int(target), event
    if len(rows) != 474:
        raise ValueError("unexpected row count")
    return rows


def generate():
    rows = load_rows()
    left, right = deque(), deque()
    state, head, ticks = 0, 0, 0
    operations, chunks = [], []
    chunk_ticks, chunk_events = 0, []

    def read():
        return right[0] if right else 0

    def move(write, direction):
        nonlocal head
        if direction == "R":
            if right:
                right.popleft()
            left.appendleft(write)
            head += 1
        elif direction == "L":
            if right:
                right.popleft()
            new_head = left.popleft() if left else 0
            right.appendleft(write)
            right.appendleft(new_head)
            head -= 1
        else:
            raise ValueError("unexpected direction")

    def one():
        nonlocal state, ticks, chunk_ticks
        write, direction, target, event = rows[state, read()]
        move(write, direction)
        state = target
        ticks += 1
        chunk_ticks += 1
        if event != "-":
            chunk_events.append(int(event))

    def snapshot():
        return state, head, list(left), list(right)

    start = snapshot()
    while state in (0, 75, 76, 77, 78):
        mode = {77: "right", 75: "left", 0: "fill"}.get(state)
        count = 0
        while mode and read() == 1:
            adjacent = (right[1] if len(right) > 1 else 0) if mode == "right" else (left[0] if left else 0)
            if adjacent != 0:
                break
            old_state = state
            one()
            one()
            if state != old_state:
                raise ValueError("pair shortcut did not return to its state")
            count += 1
        operations.append((mode, count) if count else ("one", 0))
        if not count:
            one()
        if len(operations) == CHUNK_SIZE or state not in (0, 75, 76, 77, 78):
            finish = snapshot()
            chunks.append((start, operations, finish, chunk_ticks, chunk_events))
            start = finish
            operations, chunk_ticks, chunk_events = [], 0, []
        if ticks > 10_000_000:
            raise ValueError("generation limit reached before bootstrap exit")
    if (ticks, state, head) != (2_133_492, 58, -2):
        raise ValueError("unexpected bootstrap exit")
    if any(c[4] for c in chunks):
        raise ValueError("unexpected event before exit")
    return chunks, ticks


def bools(values):
    return "[" + ", ".join("true" if x else "false" for x in values) + "]"


def config(snapshot):
    state, head, left, right = snapshot
    return f"⟨{state}, {head}, ⟨{bools(left)}, {bools(right)}⟩⟩"


def op_text(op):
    mode, count = op
    return ".one" if mode == "one" else f".{mode} {count}"


def outputs():
    chunks, ticks = generate()
    prefix = ("import PASoundness.M236FastBootstrap\n\n"
              "namespace PASoundness.M236.FastBootstrap.Certificate\n"
              "open PASoundness.M236.FiniteTape\n\n")
    data = prefix + "def bootState0 : Configuration 237 := rawSystem.initial\n\n"
    for i, (_, operations, finish, duration, events) in enumerate(chunks):
        data += f"def bootOps{i} : List Op := [" + ", ".join(map(op_text, operations)) + "]\n"
        data += f"def bootState{i + 1} : Configuration 237 := {config(finish)}\n"
        data += f"def bootTicks{i} : Nat := {duration}\n\n"
    data += "end PASoundness.M236.FastBootstrap.Certificate\n"
    result = {"M236BootCertData.lean": data}
    for part in range((len(chunks) + PART_SIZE - 1) // PART_SIZE):
        source = ("import PASoundness.M236BootCertData\n\nset_option maxRecDepth 65536\n"
                  "set_option maxHeartbeats 0\nnamespace PASoundness.M236.FastBootstrap.Certificate\n\n")
        for i in range(part * PART_SIZE, min((part + 1) * PART_SIZE, len(chunks))):
            source += (f"theorem bootChunk{i} : runOps bootState{i} bootOps{i} = "
                       f"some (bootState{i + 1}, bootTicks{i}, []) := by decide\n\n")
        source += "end PASoundness.M236.FastBootstrap.Certificate\n"
        result[f"M236BootCertPart{part:02d}.lean"] = source
    parts = (len(chunks) + PART_SIZE - 1) // PART_SIZE
    source = "".join(f"import PASoundness.M236BootCertPart{part:02d}\n" for part in range(parts))
    source += ("\nset_option maxRecDepth 65536\nset_option maxHeartbeats 0\n"
               "namespace PASoundness.M236.FastBootstrap.Certificate\n"
               "open PASoundness.M236.FiniteTape\n\n"
               "/-- The checked chunks compose to an exact silent blank-start block. -/\n"
               f"theorem bootstrap_block : rawSystem.Block rawSystem.initial {ticks} "
               f"bootState{len(chunks)} [] := by\n")
    for i in range(len(chunks)):
        source += (f"  have b{i} := (runOps_sound bootOps{i} bootState{i} bootState{i + 1} "
                   f"bootTicks{i} [] bootChunk{i}).1\n")
        if i:
            previous = "b0" if i == 1 else f"all{i - 1}"
            source += f"  have all{i} := {previous}.trans rawSystem b{i}\n"
    tick_sum = " + ".join(f"bootTicks{i}" for i in range(len(chunks)))
    source += (f"  have htime : {tick_sum} = {ticks} := by decide\n"
               f"  rw [htime] at all{len(chunks) - 1}\n"
               f"  change rawSystem.Block bootState0 {ticks} bootState{len(chunks)} []\n"
               f"  simpa only [List.nil_append] using all{len(chunks) - 1}\n\n")
    source += ("theorem related_map {z : Configuration 237} {c : Shared.Beeping.Machines.Config 237}\n"
               "    (h : Related z c) : Related ⟨mapState z.state, z.head, z.tape⟩ (mapConfig c) := by\n"
               "  rcases h with ⟨hs, hh, ht⟩\n"
               "  exact ⟨congrArg mapState hs, hh, ht⟩\n\n"
               "/-- Literal raw and quotient executions at the certified bootstrap exit.\n"
               "The finite zipper represents the whole two-way tape. -/\n"
               "theorem bootstrap_reached :\n"
               f"    Related bootState{len(chunks)} ((machineWordSystem raw rawLabels).run {ticks}) ∧\n"
               f"      Related ⟨57, -2, bootState{len(chunks)}.tape⟩ ((machineWordSystem machine machineLabels).run {ticks}) ∧\n"
               f"      (machineWordSystem raw rawLabels).prefixWord {ticks} = [] ∧\n"
               f"      (machineWordSystem machine machineLabels).prefixWord {ticks} = [] ∧\n"
               f"      (machine.system.run {ticks}).state = 57 ∧\n"
               f"      (machine.system.run {ticks}).head = -2 := by\n"
               f"  have hs := raw_run_sound {ticks}\n"
               f"  change Related (rawSystem.advance rawSystem.initial {ticks}) _ ∧\n"
               f"    rawSystem.wordFrom rawSystem.initial {ticks} = _ at hs\n"
               "  have hb := bootstrap_block\n"
               "  rw [hb.endpoint, hb.output] at hs\n"
               f"  have hstate : (raw.system.run {ticks}).state = 58 := by\n"
               "    have h := hs.1.1\n"
               "    rw [machineWordSystem_run] at h\n"
               f"    change (58 : Fin 237) = (raw.system.run {ticks}).state at h\n"
               "    exact h.symm\n"
               f"  have hhead : (raw.system.run {ticks}).head = -2 := by\n"
               "    have h := hs.1.2.1\n"
               "    rw [machineWordSystem_run] at h\n"
               f"    change (-2 : Int) = (raw.system.run {ticks}).head at h\n"
               "    exact h.symm\n"
               "  have hm : mapState 58 = 57 := by decide\n"
               f"  have hmap := map_run {ticks}\n"
               "  have hrel := related_map hs.1\n"
               "  rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels] at hrel\n"
               f"  have hz : bootState{len(chunks)}.state = 58 := rfl\n"
               f"  have hh : bootState{len(chunks)}.head = -2 := rfl\n"
               "  rw [hz, hm, hh] at hrel\n"
               "  refine ⟨hs.1, hrel, hs.2.symm, ?_, ?_, ?_⟩\n"
               f"  · rw [← prefix_eq {ticks}]; exact hs.2.symm\n"
               "  · have h := congrArg (fun c => c.state) hmap\n"
               f"    change mapState (raw.system.run {ticks}).state = (machine.system.run {ticks}).state at h\n"
               "    rw [hstate, hm] at h\n"
               "    exact h.symm\n"
               "  · have h := congrArg (fun c => c.head) hmap\n"
               "    have heq (c : Shared.Beeping.Machines.Config 237) : (mapConfig c).head = c.head := rfl\n"
               "    rw [heq, hhead] at h\n"
               "    exact h.symm\n\n"
               "/-- Compact description of the complete zero-background exit tape. -/\n"
               "def exitTape : Tape :=\n"
               "  ⟨(List.replicate 1909 [true, false]).flatten ++ [true],\n"
               "    [true, false, true, true, true, true]⟩\n\n"
               f"theorem exit_tape_checked : bootState{len(chunks)}.tape = exitTape := by decide\n\n"
               "theorem selected_exit_geometry :\n"
               f"    Related ⟨57, -2, exitTape⟩ ((machineWordSystem machine machineLabels).run {ticks}) ∧\n"
               f"      (machineWordSystem machine machineLabels).prefixWord {ticks} = [] := by\n"
               "  have h := bootstrap_reached\n"
               "  have hr := h.2.1\n"
               "  rw [exit_tape_checked] at hr\n"
               "  exact ⟨hr, h.2.2.2.1⟩\n\n"
               "end PASoundness.M236.FastBootstrap.Certificate\n")
    result["M236BootstrapCertificate.lean"] = source
    if len(chunks) < 2 or chunks[-1][1][-1] != ("one", 0):
        raise ValueError("the final chunk must end with one literal transition")
    before_ticks = chunks[-1][3] - 1
    before_total = ticks - 1
    source = ("import PASoundness.M236BootstrapCertificate\n\n"
              "set_option maxRecDepth 65536\nset_option maxHeartbeats 0\n"
              "namespace PASoundness.M236.FastBootstrap.Certificate\n"
              "open Shared.Beeping Shared.Beeping.Machines\n"
              "open PASoundness.M236.FiniteTape PASoundness.M236.Bootstrap\n\n"
              "/-- Reverse the final right move; the read/write bit there is one. -/\n"
              f"def beforeState : Configuration 237 := ⟨76, -3, moveLeft bootState{len(chunks)}.tape "
              f"(read bootState{len(chunks)}.tape)⟩\n\n"
              f"def beforeOps : List Op := bootOps{len(chunks) - 1}.dropLast\n\n"
              f"theorem beforeChunk : runOps bootState{len(chunks) - 1} beforeOps = "
              f"some (beforeState, {before_ticks}, []) := by decide\n\n"
              "/-- The complement of the five bootstrap states has no edge back into them. -/\n"
              "theorem no_reentry : ∀ (q : Fin 237) (b : Bool),\n"
              "    ¬ rawState q → ¬ rawState (raw.table.row q b).next := by decide\n\n"
              "theorem outside_forward (i k : Nat) (h : ¬ rawState (raw.system.run i).state) :\n"
              "    ¬ rawState (raw.system.run (i + k)).state := by\n"
              "  induction k with\n"
              "  | zero => simpa using h\n"
              "  | succ k ih =>\n"
              "    have hn := no_reentry (raw.system.run (i + k)).state\n"
              "      ((raw.system.run (i + k)).tape (raw.system.run (i + k)).head) ih\n"
              "    simpa only [Nat.add_succ, Machine.next_state] using hn\n\n"
              "theorem before_all (last i : Nat) (h : rawState (raw.system.run last).state)\n"
              "    (hi : i ≤ last) : rawState (raw.system.run i).state := by\n"
              "  by_cases hn : rawState (raw.system.run i).state\n"
              "  · exact hn\n"
              "  · have ho := outside_forward i (last - i) hn\n"
              "    have he : i + (last - i) = last := Nat.add_sub_of_le hi\n"
              "    rw [he] at ho\n"
              "    exact (ho h).elim\n\n"
              f"theorem before_block : rawSystem.Block rawSystem.initial {before_total} beforeState [] := by\n")
    for i in range(len(chunks) - 1):
        source += (f"  have b{i} := (runOps_sound bootOps{i} bootState{i} bootState{i + 1} "
                   f"bootTicks{i} [] bootChunk{i}).1\n")
        if i:
            previous = "b0" if i == 1 else f"all{i - 1}"
            source += f"  have all{i} := {previous}.trans rawSystem b{i}\n"
    last_prefix = len(chunks) - 2
    source += (f"  have last := (runOps_sound beforeOps bootState{len(chunks) - 1} beforeState "
               f"{before_ticks} [] beforeChunk).1\n"
               f"  have full := all{last_prefix}.trans rawSystem last\n")
    tick_sum = " + ".join(f"bootTicks{i}" for i in range(len(chunks) - 1))
    source += (f"  have htime : {tick_sum} + {before_ticks} = {before_total} := by decide\n"
               "  rw [htime] at full\n"
               f"  change rawSystem.Block bootState0 {before_total} beforeState []\n"
               "  simpa only [List.nil_append] using full\n\n"
               f"theorem before_state : (raw.system.run {before_total}).state = 76 := by\n"
               f"  have hs := raw_run_sound {before_total}\n"
               f"  change Related (rawSystem.advance rawSystem.initial {before_total}) _ ∧\n"
               f"    rawSystem.wordFrom rawSystem.initial {before_total} = _ at hs\n"
               "  rw [before_block.endpoint, before_block.output] at hs\n"
               "  have h := hs.1.1\n"
               "  rw [machineWordSystem_run] at h\n"
               f"  change (76 : Fin 237) = (raw.system.run {before_total}).state at h\n"
               "  exact h.symm\n\n"
               "/-- The checked exit time is the first departure from the bootstrap subgraph. -/\n"
               "theorem raw_first_exit :\n"
               f"    (∀ i, i < {ticks} → rawState (raw.system.run i).state) ∧\n"
               f"      ¬ rawState (raw.system.run {ticks}).state := by\n"
               "  constructor\n"
               "  · intro i hi\n"
               f"    apply before_all {before_total} i\n"
               "    · rw [before_state]; decide\n"
               "    · omega\n"
               "  · have h := bootstrap_reached.1.1\n"
               "    rw [machineWordSystem_run] at h\n"
               f"    change (58 : Fin 237) = (raw.system.run {ticks}).state at h\n"
               "    rw [← h]\n"
               "    decide\n\n"
               "theorem selected_first_exit :\n"
               f"    (∀ i, i < {ticks} → selectedState (machine.system.run i).state) ∧\n"
               f"      ¬ selectedState (machine.system.run {ticks}).state := by\n"
               "  constructor\n"
               "  · intro i hi\n"
               "    have h := congrArg (fun c => c.state) (map_run i)\n"
               "    change mapState (raw.system.run i).state = (machine.system.run i).state at h\n"
               "    rw [← h]\n"
               "    exact (mapped_state _).mp (raw_first_exit.1 i hi)\n"
               "  · have h := bootstrap_reached.2.2.2.2.1\n"
               "    rw [h]\n"
               "    decide\n\n"
               "theorem selected_first_visit :\n"
               f"    (∀ i, i < {ticks} → (machine.system.run i).state ≠ 57) ∧\n"
               f"      (machine.system.run {ticks}).state = 57 := by\n"
               "  constructor\n"
               "  · intro i hi he\n"
               "    have hb := selected_first_exit.1 i hi\n"
               "    rw [he] at hb\n"
               "    have hn : ¬ selectedState 57 := by decide\n"
               "    exact hn hb\n"
               "  · exact bootstrap_reached.2.2.2.2.1\n\n"
               "end PASoundness.M236.FastBootstrap.Certificate\n")
    result["M236FirstExit.lean"] = source
    return result, chunks, ticks


def main():
    files, chunks, ticks = outputs()
    checking = "--check" in sys.argv
    for name, source in files.items():
        path = LEAN / name
        if checking:
            if not path.is_file() or path.read_text() != source:
                raise SystemExit(f"generated certificate differs: {name}")
        elif not path.is_file() or path.read_text() != source:
            path.write_text(source)
    print(f"generated {len(chunks)} chunks claiming {ticks} raw transitions")


if __name__ == "__main__":
    main()
