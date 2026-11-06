"""Generate the full embedded-character certificate for the 284-state table.

This pins the generator input and includes every character, including the final
newline. Lean checks the embedded String equality; it does not verify a
filesystem hash, later filesystem changes, or parsing to the machine data.
"""
import argparse
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "Inputs" / "selected284-events.tm"
SOURCE_SHA256 = "0c924f63d3cdd89f97078aef409010fa868b189466ab186a17e105f81e9279aa"


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
    chars = ", ".join(map(char_literal, text))
    return ("import Std\n\n"
            "/-! Complete character content of the selected table as embedded\n"
            "by `include_str`, including its final newline. This theorem does\n"
            "not identify the parsed data or assert a later filesystem state. -/\n"
            "namespace Shared.Beeping.NPcoNP.Table284.SourceChars\n\n"
            "set_option maxRecDepth 1000000\n"
            "set_option maxHeartbeats 0\n\n"
            "def source : String := include_str \"Inputs/selected284-events.tm\"\n\n"
            "def chars : List Char := [" + chars + "]\n\n"
            "theorem source_eq_ofList : source = String.ofList chars := by rfl\n\n"
            "theorem source_toList : source.toList = chars := by\n"
            "  rw [source_eq_ofList, String.toList_ofList]\n\n"
            "end Shared.Beeping.NPcoNP.Table284.SourceChars\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "Table284SourceChars.lean")
    args = parser.parse_args()
    args.output.write_text(generate(), encoding="utf-8")


if __name__ == "__main__":
    main()
