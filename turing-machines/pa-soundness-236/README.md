# A 236-state machine for PA soundness

This package publishes **M236**, one particular deterministic, binary,
blank-tape Turing machine with an output-bit label on four transitions.
Its fixed, explicitly defined infinite-output observer accepts exactly when
every theorem of first-order Peano arithmetic is true in the standard natural
numbers:

\[
\operatorname{OmegaAccept}(M236)
\quad\Longleftrightarrow\quad
\forall \varphi\text{ a PA sentence},\quad
\mathrm{PA}\vdash\varphi\ \Longrightarrow\ \mathbb N\models\varphi.
\]

Here **ω-acceptance is a property of the entire output**, not halting, an
accepting state, infinitely many beeps, or a decision procedure for truth.
It combines a complete correctly framed record stream with a winning strategy
for each finite natural-number game. Strategies may depend on the game and
need not be computable. [Read the precise definition and examples](OBSERVER.md).

## Start here

- [Exact 472-row machine](machine.tm), including its initial configuration and
  output labels; [237-state parent](raw.tm).
- [How the machine works and why the equivalence holds](PROOF.md).
- [Verification, trust boundary, and reproduction commands](VERIFICATION.md).
- [Full Lean source](formalization/lean/PASoundness.lean), including the
  [end-to-end theorem](formalization/lean/PASoundness/PAtoCompactEndToEndProofTranslation.lean),
  [explicit observer theorem](formalization/lean/PASoundness/M236ObserverFrontDoor.lean),
  and [historical-style observer corollary](formalization/lean/PASoundness/M236HistoricalPASoundness.lean).
- [Original producer and reproduction recipe](producer/README.md),
  [source identity manifest](SOURCE-MANIFEST.json), and [attribution](ATTRIBUTION.md).

## What is fixed

| Component | Exact choice |
| --- | --- |
| Tape | One two-way-infinite tape, alphabet `{0,1}`, initially all zero |
| Start | State `0`, head at tape coordinate `0` |
| States | `0` through `235`, with one row for each state/read pair |
| Row | `state read write direction next event`; `L` or `R`; event `-` means silence |
| Output | One `0` or `1` event, at most, on an executed marked transition |
| Observation | Positive-rank addressed unary frames, complete-record and progress guards, separate finite-game strategies |
| Machine SHA-256 | `bcf4a1fd22e9959a4145688d05ec20591d97967050ad1a16beeb22a187edaedc` |

The output is not the tape symbol written by the transition. In this table,
`(134,0)` and `(136,0)` emit `1`; `(137,1)` and `(146,0)` emit `0`.
All other transitions are silent. There are no halting rows: the transition
function is total and stays in the 236 states.

## What is proved, and in what sense

The Lean endpoint has **no caller-supplied semantic bridge assumptions**. Its
proof connects the actual table to its selected record source, then to a
compact calculus, and then to genuine syntactic PA derivability and standard
`Nat` semantics. The bridge contains both proof transports and separate truth
translations; it does not manufacture an equivalence by independently assuming
or proving the two soundness statements.

Upstream reports kernel-checked builds, transitive axiom/dependency audits,
and scoped independent source reviews. This public release distinguishes those
reports from its own reproducible source and finite checks in
[VERIFICATION.md](VERIFICATION.md). It does **not** claim an independent full
Lean rebuild, an independent kernel implementation, or external human referee
certification.

This is not PA proving its own soundness. The theorem and the available
metatheoretic PA soundness proof live in Lean's stronger ambient foundations.
In those foundations one may combine them to conclude acceptance, but a finite
run cannot establish the observer condition. No independence-from-ZFC,
minimality, or state-count record is claimed.

The selected game identifier is an **H-formula code**, not a PA proof code.
The historical manuscript's normalized-PA record coding and this compact
coding are not asserted to agree record by record. The formal historical-style
observer equivalence concerns the observer on a given physical stream.

[Back to the machine index](../README.md).
