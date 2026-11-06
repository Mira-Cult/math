#!/usr/bin/env python3
"""Generate untrusted packed replay blocks after a proved checkpoint.

The new window is a left extension with the same right boundary. All emitted
replays, timings and full tape snapshots require Lean checking.
"""
import argparse
from pathlib import Path
import generate_bootstrap284_trace as trace


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--end", type=int, required=True)
    parser.add_argument("--old-base", type=int, required=True)
    parser.add_argument("--old-span", type=int, required=True)
    parser.add_argument("--base", type=int, required=True)
    parser.add_argument("--span", type=int, required=True)
    parser.add_argument("--parent-kind", choices=("Chunks", "Continue", "BulkContinue"), default="Chunks")
    parser.add_argument("--rec-depth", type=int, default=131072)
    parser.add_argument("--bulk", action="store_true")
    args = parser.parse_args()
    assert 0 < args.start < args.end and args.start % 32 == 0
    assert args.base <= args.old_base and args.base + args.span == args.old_base + args.old_span
    ops, expected = trace.generate()
    assert args.end <= len(ops) and (args.end % 32 == 0 or args.end == len(ops))
    table = Path(__file__).parent / "Inputs" / "selected284-events.tm"
    rows = {}
    for line in table.read_text(encoding="ascii").splitlines():
        if line and not line.startswith("#"):
            q, read, write, direction, target, beep = line.split()
            rows[int(q), int(read)] = int(write), direction, int(target), int(beep)
    tape: set[int] = set()
    q = head = time = 0
    last_time = expected[args.start][2]
    checkpoints = []
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
        if index > args.start and (index % 32 == 0 or index == args.end):
            assert all(args.base <= p < args.base + args.span for p in tape)
            bits = sum(1 << (p-args.base) for p in tape)
            checkpoints.append((index,q,head,time,time-last_time,bits))
            last_time = time
    base, span = args.base, args.span
    delta = args.old_base-base
    ns = f"Bootstrap284{'Bulk' if args.bulk else 'Packed'}Continue{args.end}"
    parent = (f"Bootstrap284BulkContinue{args.start}" if args.parent_kind == "BulkContinue"
              else f"Bootstrap284Packed{args.parent_kind}{args.start}")
    print(f"import Shared.Beeping.NPcoNP.{parent}")
    print("import Shared.Beeping.NPcoNP.Bootstrap284PackedRebase")
    if args.bulk:
        print("import Shared.Beeping.NPcoNP.Bootstrap284BulkReplay")
    print("\n/-! Generated continuation; each asserted block requires Lean checking. -/")
    print(f"namespace Shared.Beeping.NPcoNP.{ns}")
    for name in ("Shared.Beeping Shared.Beeping.Machines PASoundness", "Shared.Beeping.NPcoNP.Table284", "Shared.Beeping.NPcoNP.NativeHalfScan", "Shared.Beeping.NPcoNP.Bootstrap284PackedStep", "Shared.Beeping.NPcoNP.Bootstrap284PackedScans", "Shared.Beeping.NPcoNP.Bootstrap284PackedRebase", "Shared.Beeping.NPcoNP.Bootstrap284TraceData", f"Shared.Beeping.NPcoNP.{parent}"):
        print("open " + name)
    if args.bulk:
        print("open Shared.Beeping.NPcoNP.Bootstrap284BulkReplay")
    print(f"set_option maxRecDepth {args.rec_depth}\nset_option maxHeartbeats 20000000")
    print(f"\ndef startConfig : Packed := extendLeft {delta} output{args.start}")
    print(f"theorem start_segment : silentSegment machine (machine.system.run 0) (toConfig ({base}) {span} startConfig) {expected[args.start][2]} := by")
    print(f"  have h : toConfig ({base}) {span} startConfig=toConfig ({args.old_base}) {args.old_span} output{args.start} := by")
    print(f"    simpa [startConfig] using toConfig_extendLeft ({args.old_base}) {args.old_span} {delta} output{args.start}")
    print(f"  rw [h]\n  exact blank_start_{args.start}")
    prev, prevtime = args.start, expected[args.start][2]
    replay = "replayBulk" if args.bulk else "replayPacked"
    for index,q,head,time,duration,bits in checkpoints:
        block_size = index-prev
        prevconfig = "startConfig" if prev == args.start else f"output{prev}"
        prevproof = "start_segment" if prev == args.start else f"blank_start_{prev}"
        print(f"\ndef output{index} : Packed := ⟨{q},{head},{hex(bits)}⟩")
        print(f"theorem checked{index} : {replay} ({base}) {span} ((ops.drop {prev}).take {block_size}) {prevconfig} = some (output{index},{duration}) := by decide")
        print(f"theorem segment{index} : silentSegment machine (toConfig ({base}) {span} {prevconfig}) (toConfig ({base}) {span} output{index}) {duration} :=\n  ({replay}_sound ({base}) {span} ((ops.drop {prev}).take {block_size}) {prevconfig} output{index} {duration} checked{index}).2")
        print(f"theorem blank_start_{index} : silentSegment machine (machine.system.run 0) (toConfig ({base}) {span} output{index}) {time} := by\n  have h := segAdd machine _ _ _ {prevtime} {duration} {prevproof} segment{index}\n  simpa using h")
        prev, prevtime = index, time
    print(f"end Shared.Beeping.NPcoNP.{ns}")
    print(f"\n#print axioms Shared.Beeping.NPcoNP.{ns}.blank_start_{args.end}")


if __name__ == "__main__":
    main()
