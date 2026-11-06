# Complete native beeper: preservation and progress

The selected machine in this package is deterministic, binary, single-tape,
blank-start and total, with a two-way infinite tape and L/R moves. Its exact
physical count and table identities are recorded in README (historical reference: `README.md`; outside this selected-only export) and
the literal cost ledger (historical reference: `evidence/physical-ledger.json`; outside this selected-only export). Every state is paid;
there is no excluded halt state, supplied program image, external verifier
or preloaded certificate. Its physical execution is infinite and

> The designated transition is applied finitely often if and only if NP = coNP.

This proof composes conventional mathematical arguments and finite replayable
certificates. Executable tests, independent model-agent reviews, exact Git
bindings and remote CI remain separate evidence categories.

## Unchanged mathematical search

The selected source remains `../source/certificate_popfirst_power.py`,
SHA-256 `96f254475ce226a2d5783b259abf0b414ae8d119c4e01430d48adf3fe3f60ac1`.
It is exactly the source of the reviewed 446-state producer
`582c0a1a6ecb2442da3bb7c07588fb6322847a5f`. The
[source theorem](../source/PROOF.md) therefore applies without changing the
reference language, candidate clocks, enumerated inputs or event controller.

For completeness, A(e,x,C) enumerates the C-bit certificates on the simulated
negative half-tape until acceptance or exhaustive failure. For each certificate
it simulates a total deterministic relative-direction description for C steps.
The physical blank-start program generates all
certificates and bounds itself. Every acceptance call finishes for arbitrary
finite naturals, including zero clocks and malformed descriptions. The
reference K(Y)=A(2^n+value(Y),0,n) is NP-complete under the proved guarded
verifier, finite writer and complete-prefix padding construction.

Candidate j accepts E(Y)=1^n0Y with clock (n+1)^j. The complete-prefix padding
and one-step empty-input wrapper cover every polynomial complement verifier.
A candidate is correct exactly when its language is the complement of K.
Reference/candidate equality is either an unsoundness or incompleteness
witness. Every wrong candidate has a finite witness, and exhaustive input
enumeration reaches it after finitely many terminating checks. A least
correct candidate gives finitely many source beeps and an infinite silent
tail of progressing checks; absence of any correct candidate gives infinitely
many beeps. Correct-candidate existence is equivalent to NP = coNP.

The rejected clock and codec experiments are comparisons only. They do not
replace any premise of this selected theorem.

## Native half/parity and compiler storage

The inherited source compiler, direct call arguments, final-return forwarding,
tuple captures, affine arithmetic and source-CFG allocation retain their
reviewed contracts. The new native operation on an unbounded natural x is

    x := floor(x/2); successful conditional return iff old x is odd.

Its tag deliberately distinguishes it from ordinary decrement. Both the
compiler's abstract analysis and the independent certificate replay use the
true quotient/parity transfer, even though the physical conditional path
encoding is shared with DECNZ.

The [native proof](../compiler/native/PROOF.md) establishes the literal unary
block algorithm. The split-block invariant decreases the unprocessed input
by two on every cycle. Each suffix sweep has a finite delimiter and preserves
all other original register values. The exact full-tape result includes
ceil(x/2) appended zero reserve blocks; this side effect is admitted by the
runtime representation and is not silently discarded from the invariant.
The kernel uses 15 literal binary control states, with separately counted
selection, preparation, operation entries and return paths.

The separate native selector uses the preserved single-separator preparation
ABI. Its operands are placed first by an explicit finite bank permutation,
and every ordinary entry/index row is regenerated for that layout. The
shared ordinary selector and its distinct blank-bootstrap aliases retain
their contracts. Every preparation, selection, suffix and return scan ends
at a finite specified delimiter, for arbitrary finite register values.

The native quotient/remainder lowering replaces a simultaneous pair by
clearing the remainder, applying native half in place and incrementing the
remainder on odd success. The native unary-record loop consumes each one
and its terminating zero with this same operation. The generic half kernel
still supports ordinary inherited callers. The original source interference
proof supplies disjointness before the later explicit coalescence stage.
All source effects, tuple evaluation and call evaluation retain their order.

## Exact certificate stages

The emitted intermediate grammars make every domain boundary explicit:

1. The original source allocation and native-aware zero-entry certificate
   use the original register carrier. The latter ends at
   `pre-control-grammar.json`. Its abstract domain is zero, one and at least
   two, with both native parity outcomes checked.
2. The fixed finite-control plan produces `pre-projection-grammar.json`.
   The [finite-jump proof](../GRAMMAR_PROOF.md) preserves the entry, each
   ordered retained operation and both outcomes of every conditional.
   Administrative jump-only cycles are rejected, so erased segments are finite.
3. The [bank projection](../compiler/native/BANK_PROOF.md) produces
   `pre-coalescence-grammar.json`. Only coordinates absent from every retained
   ordinary/native operation are omitted. They remain zero from the all-zero
   entry, and the inverse interpretation inserts exactly those zero coordinates.
4. `coalescence-invariant.json` is an independently replayable post-fixed
   invariant over that precise retained grammar. The fixed groups are checked
   against every reachable ordinary/native operation. Every partner of the
   operated-on member must be definitely zero at its pre-operation occurrence.
5. `bank-coalescence.json` maps the ghost carrier to physical classes. The
   final `grammar.json` contains renamed operations and shared identical pairs.
   Its retained control graph equals the mapped original graph, with the
   same entry and both conditional successors.

`control-certificate.json` and `bank-coalescence.json` together bind each
adjacent grammar hash, the fixed control plan, the fixed group plan and the
invariant. The selected producer runs no
grammar or grouping search. A shorter intermediate graph is never substituted
for a complete physical count.

## Class sums and cofinal simulation

For every physical class C, the representation is

\[
    V(C)=\sum_{x\in C}v(x),
\]

where v is the old logical store carried as ghost state in the proof. At the
all-zero entry this relation holds. At an operation on x, all of its partners
are zero by the checked invariant, hence its physical class has exactly v(x).
INC, ordinary DECNZ and native half therefore read the same value, choose
the same conditional outcome and update the class sum correctly. Every
other class is preserved. Control operations and beeps change no values.
Induction gives the same ordered source events and successors forever.

This is the [coalescence proof](../compiler/native/COALESCENCE_PROOF.md).
It does not assert that every old coordinate can be read as an unconditional
alias of the physical cell. Inactive coordinates may be zero while another
member holds a positive physical value. Tests and physical observations
compare against sums from the independently executed ghost grammar. The
induction also proves at most one member of a class is nonzero on the admitted
run, but the sum relation is the canonical representation invariant.

The renamed graph preserves each retained primitive and both successors;
finite administrative contraction preserves cofinal progress. Each retained
primitive terminates physically on every finite admitted bank by its ordinary
or native proof. Each finite source stage therefore has a finite physical
simulation, including every later input comparison after any final beep.
The argument cannot silently stop at a checkpoint that might never be reached.

## Paid blank entry and event adaptation

The unchanged five-state bootstrap, full register selector, program grammar,
native kernel, arithmetic, scratch roles and event adaptation all appear in
the literal raw table. Its actual blank run is separately replayed on the
selected bytes. It reaches the source entry with head -3818 and one-cells
{-3821,-3820} union {3,5,...,3821}, before any event. This supplies the all-zero
physical class store and enough finite reserve capacity. The register count
and every source path are checked against the paid bootstrap's bounds; they
are bounds on the finite program, not bounds on any natural value or search.

The exact raw-to-B quotient checks both rows of every state and preserves
write, move, target and B color. The B machine starts outside B and is total.
Every B entrance is followed by its exit exactly one physical step later,
and every B exit has that unique preceding entrance. Moving the mark to
ingress preserves the finite/infinite distinction with a one-step time shift.
The final exact event-colored quotient checks every event flag as well.
The unique final marked row and its identity are given in the selected table
and README; the event is the application of that row, not state entry under
an unstated convention.

The resulting binary machine runs forever in both complexity-theoretic cases.
Eventual silence refers solely to the designated mark. Finite initialization,
other finitely visited states and bounded quiet prefixes do not define its
quasihalting property or decide NP versus coNP.
