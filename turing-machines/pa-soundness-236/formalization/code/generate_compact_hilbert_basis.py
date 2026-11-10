#!/usr/bin/env python3
"""Reproduce the finite Lean AX7/MP basis from the pinned recovered proof terms.

This is a textual data translator, not a trusted proof checker. Its output is
checked against the exact CompactProof constructors by Lean. It does not invoke
Coq, a proof search engine, or any external process.

Usage:
  python generate_compact_hilbert_basis.py --source NumericHilbert238.v --output basis.lean
"""

import argparse
import hashlib
from pathlib import Path
import re

SOURCE_SHA256 = "fd577e5737cfa733c924bb832d2742ab7ead223c3837a27956c97d0076401223"
TARGETS = (25, 36, 196, 4520, 4535)

HEADER = "import PASoundness.CompactProof\n\n/-!\nFinite AX7/MP certificates for an ordinary implicational Hilbert basis.\nPorted from the explicit dependency closure of NumericHilbert238.v in the\nrecovered PA238 source archive. The Coq source states that its bounded\nunification search independently recomputed detachment edges; B/S target\nformulas were read from Jeff's CD254 at c132d7eae8158cd3a9850ea3eb7251158c3dd821.\nThis module checks the displayed proof objects anew in Lean, against the exact\ncompact numeric axiom and modus ponens constructors. No Coq theorem is trusted.\nSource file SHA-256: fd577e5737cfa733c924bb832d2742ab7ead223c3837a27956c97d0076401223\n-/\nnamespace PASoundness.CompactHilbertBasis\nopen CompactProof\nattribute [local irreducible] imp Cantor.pair Cantor.triangle\n\nprivate def mpCode (a b : Nat) (da : KDerivation a) (dab : KDerivation (imp a b)) :\n    KDerivation b := .mp da dab\n\nprivate def ax7 (a b c u : Nat) :\n    KDerivation (imp (imp (imp c u) a) (imp (imp a c) (imp b c))) := by\n  change KDerivation (axiomCode 7 a b c u)\n  exact .axiom ⟨7, by decide⟩ a b c u\n\n"

FOOTER = 'def identity (a : Nat) : KDerivation (imp a a) := r8_certificate_25 a\n\ndef weakening (a b : Nat) : KDerivation (imp a (imp b a)) := r8_certificate_36 a b\n\ndef peirce (a b : Nat) : KDerivation (imp (imp (imp a b) a) a) := r8_certificate_196 a b\n\ndef composition (a b c : Nat) :\n    KDerivation (imp (imp a b) (imp (imp b c) (imp a c))) := r8_certificate_4520 a b c\n\ndef distribution (a b c : Nat) :\n    KDerivation (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := r8_certificate_4535 a b c\n\nend PASoundness.CompactHilbertBasis\n'


def translate(text: str) -> str:
    replacements = {
        "Compiler238.derivable": "KDerivation",
        "Compiler238.derives_mp": "mpCode",
        "Compiler238.derives_r8": "ax7",
        "wim": "imp",
        "nat": "Nat",
    }
    for source, target in replacements.items():
        text = re.sub(r"(?<![A-Za-z0-9_])" + re.escape(source) + r"(?![A-Za-z0-9_])", target, text)
    return text


def generate(source: Path) -> str:
    data = source.read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != SOURCE_SHA256:
        raise ValueError(f"source SHA-256 {actual} differs from pinned {SOURCE_SHA256}")
    text = data.decode("utf-8")
    pattern = re.compile(
        r"Local Lemma (r8_certificate_\d+) (\([^\n]+\)) :\s*(.*?)\.\s*"
        r"Proof\.\s*exact (.*?)\.\s*Qed\.", re.S)
    entries = {name: (parameters, statement.strip(), body.strip())
               for name, parameters, statement, body in pattern.findall(text)}
    required = {f"r8_certificate_{n}" for n in TARGETS}
    pending = list(required)
    while pending:
        name = pending.pop()
        if name not in entries:
            raise ValueError(f"missing explicit proof object {name}")
        for dependency in re.findall(r"r8_certificate_\d+", entries[name][2]):
            if dependency not in required:
                required.add(dependency)
                pending.append(dependency)
    if len(required) != 97:
        raise ValueError(f"unexpected dependency closure size {len(required)}")
    output = [HEADER]
    for name, (parameters, statement, body) in entries.items():
        if name in required:
            output.append(f"private def {name} {translate(parameters)} :\n"
                          f"  {translate(statement)} :=\n  {translate(body)}\n\n")
    output.append(FOOTER)
    return "".join(output)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = generate(args.source)
    args.output.write_text(output, encoding="utf-8")
    print(f"wrote 97 explicit proof schemas; SHA-256 {hashlib.sha256(output.encode()).hexdigest()}")


if __name__ == "__main__":
    main()
