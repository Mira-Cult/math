"""Generate candidate source-line/pair chunks and Lean row certificates.

The generator is untrusted. Lean independently verifies every emitted row,
the ordering/composition and exact equality to the existing numeric table.
The source bytes-to-lines binding is a separate obligation.
"""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "Inputs/selected284-events.tm"
EXPECTED = "0c924f63d3cdd89f97078aef409010fa868b189466ab186a17e105f81e9279aa"
WIDTH = 10
STATES = 284


def rawrow(fields):
    state, read, write, direction, target, beep = fields
    assert state.isascii() and state.isdecimal() and target.isascii() and target.isdecimal()
    assert read in ("0", "1") and write in ("0", "1") and beep in ("0", "1")
    assert direction in ("L", "R")
    boolean = lambda v: "true" if v else "false"
    return int(state), int(read), (
        f"({boolean(write == '1')}, ({boolean(direction == 'R')}, "
        f"({int(target)}, {boolean(beep == '1')})))"
    )


def right_append(names):
    return " ++ ".join(names)


def generate(out: Path):
    src = SOURCE.read_bytes()
    if hashlib.sha256(src).hexdigest() != EXPECTED:
        raise ValueError("unexpected pinned source hash")
    text = src.decode("ascii")
    assert text.endswith("\n") and "\r" not in text
    lines = text.splitlines()
    assert lines[:5] == ["#! format beeper-events-v1", "#! states 284",
                         "#! start 0", "#! blank 0", "#! head 0"]
    assert len(lines) == 5 + 2 * STATES
    raw_lines = lines[5:]
    pairs = []
    for i in range(STATES):
        a, b = (rawrow(raw_lines[2*i].split(" ")),
                rawrow(raw_lines[2*i+1].split(" ")))
        assert a[:2] == (i, 0) and b[:2] == (i, 1)
        pairs.append(f"({a[2]}, {b[2]})")

    out.mkdir(parents=True, exist_ok=True)
    count = (STATES + WIDTH - 1) // WIDTH
    buf = ["import Shared.Beeping.NPcoNP.Table284Data", "", 
           "/-! Generated candidate lines and row pairs. Lean checks the pair",
           "identity below; the input-file-to-lines identity is separate. -/",
           "namespace Shared.Beeping.NPcoNP.Table284LineData",
           "open Shared.Beeping.TableBits", "set_option maxRecDepth 8192", ""]
    for j in range(count):
        lo, hi = j * WIDTH, min((j + 1) * WIDTH, STATES)
        buf.append(f"def lines{j:02d} : List (List Char) := [")
        buf.extend(f"  {json.dumps(x)}.toList," for x in raw_lines[2*lo:2*hi])
        buf[-1] = buf[-1].removesuffix(",")
        buf.extend(["]", f"def pairs{j:02d} : List RawPair := ["])
        buf.extend(f"  {x}," for x in pairs[lo:hi])
        buf[-1] = buf[-1].removesuffix(",")
        buf.extend(["]", ""])
    buf.extend([
        "def lines : List (List Char) := " + right_append([f"lines{j:02d}" for j in range(count)]),
        "def pairs : List RawPair := " + right_append([f"pairs{j:02d}" for j in range(count)]),
        "", "theorem pairs_eq_data : pairs = Table284.data.2 := by rfl", "",
        "end Shared.Beeping.NPcoNP.Table284LineData", "",
    ])
    (out / "Table284LineData.lean").write_text("\n".join(buf))

    for j in range(count):
        lo, hi = j * WIDTH, min((j + 1) * WIDTH, STATES)
        ns = f"Table284RowShard{j:02d}"
        code = ["import Shared.Beeping.NPcoNP.Table284RowCert",
                "import Shared.Beeping.NPcoNP.Table284LineData", "",
                "/-! Kernel-check a finite contiguous chunk of table rows. -/",
                f"namespace Shared.Beeping.NPcoNP.{ns}",
                "open Table284Ascii.RowCert Table284LineData", "",
                "set_option maxRecDepth 8192", "set_option maxHeartbeats 0", "",
                f"theorem checked : Chunk 284 {lo} lines{j:02d} pairs{j:02d} {hi} := by",
                f"  unfold lines{j:02d} pairs{j:02d}"]
        for _ in range(lo, hi):
            code.extend(["  refine Chunk.cons ?_ ?_", "  · constructor <;> decide"])
        code.append(f"  exact Chunk.nil {hi}")
        code.extend(["", f"end Shared.Beeping.NPcoNP.{ns}", ""])
        (out / f"{ns}.lean").write_text("\n".join(code))

    names = [f"Table284RowShard{j:02d}.checked" for j in range(count)]
    cert = names[-1]
    for name in reversed(names[:-1]):
        cert = f"Chunk.append {name} ({cert})"
    coverage = [f"import Shared.Beeping.NPcoNP.Table284RowShard{j:02d}" for j in range(count)]
    coverage += ["", "/-! Row coverage for the generated line data, not yet a",
                 "binding of those lines to the preserved source characters. -/",
                 "namespace Shared.Beeping.NPcoNP.Table284RowCoverage",
                 "open Table284Ascii.RowCert Table284LineData", "",
                 "set_option maxRecDepth 8192", "",
                 "theorem chunk : Chunk 284 0 lines pairs 284 := by",
                 "  unfold lines pairs", "  simp only [List.append_assoc]", f"  exact {cert}", "",
                 "theorem parsed_rows : Table284Ascii.rows 284 0 (lines ++ [[]]) =",
                 "    some Table284.data.2 := by",
                 "  simpa only [pairs_eq_data] using rows_complete 284 0 lines pairs chunk", "",
                 "end Shared.Beeping.NPcoNP.Table284RowCoverage", ""]
    (out / "Table284RowCoverage.lean").write_text("\n".join(coverage))
    print(f"source={EXPECTED} states={STATES} chunks={count}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    generate(parser.parse_args().output_dir)
