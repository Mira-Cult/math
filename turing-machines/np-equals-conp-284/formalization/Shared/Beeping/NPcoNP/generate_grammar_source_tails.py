"""Generate shared complete-input suffixes at grammar-node boundaries.

The positions are untrusted generator output: Lean checks their concatenated
character content against the already certified `SourceChars.chars`. The
result does not itself parse JSON or identify the AST.
"""
import argparse
import hashlib
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "Inputs" / "parent290-grammar.json"
SOURCE_SHA256 = "6520062bc16643402072f386590392688ed6cb47e509a6b98dc5acb982d6b9d3"


def char_literal(char: str) -> str:
    escapes = {"\n": r"\n", "\r": r"\r", "\t": r"\t",
               "'": r"\'", "\\": r"\\"}
    return "'" + escapes.get(char, char) + "'"


def generate() -> str:
    data = SOURCE.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != SOURCE_SHA256:
        raise ValueError(f"unexpected source SHA-256: {digest}")
    text = data.decode("ascii")
    if not text.endswith("\n") or not all(c in "\n\r\t" or 32 <= ord(c) < 127 for c in text):
        raise ValueError("expected printable ASCII text ending in a newline")
    starts = [m.start() for m in re.finditer(r"(?m)^    \[\n", text)]
    if len(starts) != 160:
        raise ValueError(f"expected 160 node starts, got {len(starts)}")
    footer = text.index('  ],\n  "registers"', starts[-1])
    cuts = [0, *starts, footer, len(text)]
    if cuts != sorted(set(cuts)):
        raise ValueError("node/footer boundaries overlap or are out of order")
    parts = [text[a:b] for a, b in zip(cuts, cuts[1:])]
    assert "".join(parts) == text and len(parts) == 162
    lines = [
        "import Shared.Beeping.NPcoNP.Grammar284SourceChars", "",
        "/-! Complete embedded source divided into header, 160 node entries,",
        "and footer by generated named suffixes. These are literal character",
        "definitions, not a JSON parser or source-to-AST proof. -/", "",
        "namespace Shared.Beeping.NPcoNP.Grammar284.SourceTails", "",
        "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
        f"def tail{len(parts)} : List Char := []", "",
    ]
    for i in range(len(parts) - 1, -1, -1):
        prefix = "".join(f"{char_literal(c)} :: " for c in parts[i])
        lines.append(f"def tail{i} : List Char := {prefix}tail{i+1}")
    lines.extend([
        "", "/-- Every character, including the final newline, is covered. -/",
        "theorem all_chars : SourceChars.chars = tail0 := by rfl", "",
        "theorem source_toList : SourceChars.source.toList = tail0 := by",
        "  rw [SourceChars.source_toList, all_chars]", "",
        "end Shared.Beeping.NPcoNP.Grammar284.SourceTails", "",
    ])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "Grammar284SourceTails.lean")
    args = parser.parse_args()
    args.output.write_text(generate(), encoding="utf-8")


if __name__ == "__main__":
    main()
