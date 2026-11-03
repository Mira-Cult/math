# A 285-state beeper for P versus NP

An explicit deterministic, two-symbol, single-tape Turing machine, started on
the wholly blank two-way tape. Its table has 285 states and 570 transitions.
It never halts. Instead, one particular transition is designated a **beep**:

> The machine emits finitely many beeps if and only if P = NP.
> Equivalently, it emits infinitely many beeps if and only if P ≠ NP.

This is a reduction of the question to an infinite-run property, **not a
resolution of P versus NP**. No finite quiet observation establishes P = NP.

## Start here

- [Proof guide](PROOF.md): the argument in ordinary mathematical language.
- [Interface audit](INTERFACE.md): what to inspect to check that Lean formalizes
  this literal machine, its actual blank start, and the intended complexity classes.
- [The exact marked table](events.tm) and [286-state companion](companion.tm).
- [Formalization](formalization/): the unchanged local dependency closure of the
  selected Lean endpoint, certificate generators, frozen inputs, and public dependency pins.
- [Reproduction and verification status](VERIFICATION.md).
- [Attribution](ATTRIBUTION.md), [provenance](PROVENANCE.json), and
  [source inventory](SOURCE-MANIFEST.json).

## Exact machine convention

States are 0 through 284. The head starts at integer position 0 in state 0,
and every tape cell initially contains 0. A row gives
`state read write direction next-state event-flag`. Every state/read pair
has exactly one row. Moves are one cell left or right; there are no halting rows.

The sole marked row is `121 1 0 L 1 1`. A beep means taking **that transition**,
not visiting an arbitrary state and not taking both exits of state 1.
Time `t` labels the transition leaving the configuration after `t` steps.
The first beep is at zero-based transition index 89,844,409, which is the
89,844,410th executed transition when counting from 1.

The marked-table SHA-256 is
`1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7`.
The companion has 286 states, not 285; its exiting-B observation is shifted
one step later. Its event-preserving quotient is separately formalized.

## The formal statement and its boundaries

The principal statement is
[`LiteralEndpoint.selected_literal_endpoint`](formalization/Shared/PNP/Record285/LiteralEndpoint.lean).
It joins the literal-row binding, exact event row, blank start, total execution,
and both P/NP event polarities in one closed theorem. It does not assume a
compiler-correctness certificate, a wrapper theorem, P = NP, or P ≠ NP as a premise.

The physical/source connection is stronger than a sampled-event comparison:
it relates the complete tape and absolute head at source-action boundaries,
with strictly positive finite segments, cofinal boundary times, and exact
event accounting. Under P = NP, late silent work consists of continued correct
comparisons by one fixed candidate, not a stuck administrative loop.

The source is pinned to revision
`576f0f2d69d37e4ba29d75ea712ddac6174832ca`. The publication is a source release,
not a claim of independent human mathematical review. Read
[VERIFICATION.md](VERIFICATION.md) for the exact build and audit status.
The producer Python AST has not itself been given a checked translation into
the Lean source model. The theorem connects the frozen literal table through
checked intermediate graphs directly to the Lean-defined source.

## Quick checks

From this directory, with Python 3.11 or newer:

```sh
python3 verify.py
```

For Lean, install the official toolchain named in `formalization/lean-toolchain`
and run the commands in [VERIFICATION.md](VERIFICATION.md). Only public upstream
dependencies are needed. No access to the original private research repository
is required to read or build this package.
