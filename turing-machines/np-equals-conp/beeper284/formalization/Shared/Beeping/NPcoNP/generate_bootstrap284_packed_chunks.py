#!/usr/bin/env python3
"""Generate untrusted 32-action packed replay blocks for a bootstrap prefix.

The emitted Lean verifies each input, output, duration, and silent physical
segment. The generator is not part of the trusted proof path.
"""
import argparse
from pathlib import Path
import generate_bootstrap284_trace as trace


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--end", type=int, required=True)
    parser.add_argument("--base", type=int, required=True)
    parser.add_argument("--span", type=int, required=True)
    parser.add_argument("--rec-depth", type=int, default=32768)
    args = parser.parse_args()
    assert args.end > 0 and args.rec_depth > 0
    assert args.base <= 0 < args.base + args.span
    ops, expected = trace.generate()
    assert args.end <= len(ops)
    assert args.end % 32 == 0 or args.end == len(ops)
    table = Path(__file__).parent / "Inputs" / "selected284-events.tm"
    rows = {}
    for line in table.read_text(encoding="ascii").splitlines():
        if line and not line.startswith("#"):
            q, read, write, direction, target, beep = line.split()
            rows[int(q), int(read)] = int(write), direction, int(target), int(beep)
    tape: set[int] = set()
    q = head = time = 0
    checkpoints = []
    last_time = 0
    for index, (op, count) in enumerate(ops[:args.end], 1):
        for _ in range(1 if op == "single" else 2 * count):
            assert args.base <= head < args.base + args.span
            write, direction, q, beep = rows[q, int(head in tape)]
            assert beep == 0
            if write:
                tape.add(head)
            else:
                tape.discard(head)
            head += 1 if direction == "R" else -1
            time += 1
        assert (q, head, time) == expected[index]
        if index % 32 == 0 or index == args.end:
            assert all(args.base <= p < args.base + args.span for p in tape)
            bits = sum(1 << (p-args.base) for p in tape)
            checkpoints.append((index,q,head,time,time-last_time,bits))
            last_time = time
    ns = f"Bootstrap284PackedChunks{args.end}"
    base, span = args.base, args.span
    print("import Shared.Beeping.NPcoNP.Bootstrap284PackedScans")
    print("import Shared.Beeping.NPcoNP.Bootstrap284TraceData")
    print("\n/-! Generated packed chunk inputs; each assertion requires Lean checking. -/")
    print(f"namespace Shared.Beeping.NPcoNP.{ns}")
    for name in ("Shared.Beeping Shared.Beeping.Machines PASoundness", "Shared.Beeping.NPcoNP.Table284", "Shared.Beeping.NPcoNP.NativeHalfScan", "Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot", "Shared.Beeping.NPcoNP.Bootstrap284PackedStep", "Shared.Beeping.NPcoNP.Bootstrap284PackedScans", "Shared.Beeping.NPcoNP.Bootstrap284TraceData"):
        print("open " + name)
    print(f"set_option maxRecDepth {args.rec_depth}\nset_option maxHeartbeats 20000000")
    print("\ndef output0 : Packed := ⟨0,0,0⟩")
    print(f"theorem packed_initial : toConfig ({base}) {span} output0=machine.system.run 0 := by")
    print("  have hz : machine.start=(0 : Fin 284) := Fin.ext machine_starts_zero.1")
    print(f"  have hb : bitSnapshot ({base}) {span} 0 = (fun _ => false) := by")
    print("    funext p\n    simp [bitSnapshot]")
    print(f"  change cfg 0 0 (bitSnapshot ({base}) {span} 0)=machine.initial")
    print("  rw [hb]\n  simp [Machine.initial,cfg,hz,machine_starts_zero.2.1,machine_starts_zero.2.2]")
    print(f"theorem blank_start_0 : silentSegment machine (machine.system.run 0) (toConfig ({base}) {span} output0) 0 := by")
    print("  rw [packed_initial]\n  simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]")
    prev, prevtime = 0, 0
    for index,q,head,time,duration,bits in checkpoints:
        block_size = index-prev
        print(f"\ndef output{index} : Packed := ⟨{q},{head},{hex(bits)}⟩")
        print(f"theorem checked{index} : replayPacked ({base}) {span} ((ops.drop {prev}).take {block_size}) output{prev} = some (output{index},{duration}) := by decide")
        print(f"theorem segment{index} : silentSegment machine (toConfig ({base}) {span} output{prev}) (toConfig ({base}) {span} output{index}) {duration} :=\n  (replayPacked_sound ({base}) {span} ((ops.drop {prev}).take {block_size}) output{prev} output{index} {duration} checked{index}).2")
        print(f"theorem blank_start_{index} : silentSegment machine (machine.system.run 0) (toConfig ({base}) {span} output{index}) {time} := by\n  have h := segAdd machine _ _ _ {prevtime} {duration} blank_start_{prev} segment{index}\n  simpa using h")
        prev, prevtime = index, time
    print(f"end Shared.Beeping.NPcoNP.{ns}")
    print(f"\n#print axioms Shared.Beeping.NPcoNP.{ns}.blank_start_{args.end}")


if __name__ == "__main__":
    main()
