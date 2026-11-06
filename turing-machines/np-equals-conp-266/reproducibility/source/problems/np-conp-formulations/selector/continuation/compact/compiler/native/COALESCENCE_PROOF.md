# Zero-partner register coalescence

This is a representation change after zero-entry/control rewriting and
unused-bank projection. It leaves the mathematical source, native arithmetic
kernel, event convention and the prior selected machines unchanged. It is
stronger than deleting unused registers: distinct logical coordinates can
share one physical block, under an explicit invariant checked at every
admitted primitive invocation.

## Original carrier and invariant

Let G be the full retained grammar after bank projection, with finite
register set R and all-zero entry. Ordinary primitives are INC and DECNZ;
the native tagged primitive replaces x by floor(x/2), taking its successful
conditional return exactly when old x is odd. Breaks, continues and beeps
modify no register. All values remain unbounded naturals.

The producer computes a zero/one/many post-fixed invariant on every unfolded
primitive/control occurrence of G. The separately replayed identity-contextual
certificate includes the zero initial state and all ordinary, native-parity
and administrative successors. A missing abstract state is an unreachability
claim established by closure from that zero entry; it is not an assumed
zero value. The native transfer is the one proved in `PROOF.md`: zero has
only an even zero image; one has only an odd zero image; at least two has
one-or-many images on either parity outcome. Representatives 0 through5
cover all these class images in the no-search checker.

Partition R into nonempty classes. The admission rule is:

> At every invariant-reachable primitive occurrence operating on x, every
> other member y of x's class has abstract mask exactly1, meaning y=0.

This rule applies to INC, both DECNZ outcomes and both native half outcomes.
All reached operations are checked, including singleton classes; only
nontrivial zero-partner obligations need listing. Every other occurrence
has an explicit unreachable abstract state and cannot be reached from the
admitted zero entry. Every physical transition is still emitted and counted.

The finite conflict graph is only a way to find admissible classes. It puts
an edge between x and y whenever a reached operation on either coordinate
does not prove the other zero. A proper coloring supplies a candidate
partition. An explicit group plan can instead be supplied. In either case
the producer rechecks the complete partition and the per-operation admission
rule; a proposed grouping never bypasses that check.

## Physical class-sum relation

For an original logical store v, define the new physical value of class C by

\[
    V(C)=\sum_{x\in C}v(x).
\]

All sums are finite natural numbers because the register inventory is finite.
At the zero entry this relation holds and all physical classes are zero.
Induct on an execution step of the original grammar.

If the step operates on x in C, the admitted invariant proves every other
member of C zero at that occurrence. Thus V(C)=v(x). The new primitive reads
exactly the original operand value. INC adds one on both sides. DECNZ makes
the same zero/nonzero decision and subtracts one in the same case. Native
half makes the same parity decision and replaces both values by the same
quotient. Only x changes logically and only C changes physically, so the
class-sum relation is preserved. Other classes remain unchanged. A control
or beep step changes no values and retains the relation.

Consequently the same successor is chosen at every ordinary/native
conditional, and the same source events occur in the same order. This
forward simulation does not require recovering every old coordinate from
one physical cell without additional logical state. The old coordinates
are **ghost values** carried by the proof. In particular an inactive member
that is logically zero must not be reported as the current physical class
value when another member is active. A finite observation of the new bank
is compared with class sums of the original grammar, not with unconditional
flat aliases of every original variable.

The same induction proves that at most one logical member of each class is
nonzero along the admitted run: this holds initially, and any operation on
one member has all partners zero beforehand and changes only that member.
The explicit sum relation remains the canonical invariant, including the
all-zero case and either outcome of the native primitive.

## Renamed grammar and physical bank

Each retained ordinary/native operand name is replaced by its class name.
Control labels, primitive occurrence order and conditional edges are left
unchanged. The final finite interning pass only shares identical renamed
binary pairs. The certificate compares the complete retained control graph
against the original graph with operand labels mapped through the explicit
class map, including both outcomes of every conditional. It also retains
the original entry and rejects administrative jump cycles. No semantic
claim follows merely from a shorter grammar or fewer register names.

Classes containing native operands form the beginning of the physical bank,
so the separate paid native selector continues to address its finite operand
prefix. The full INC/DECNZ entry/index inventory is rebuilt for the new
class order, and the native operation entries are rebuilt for the mapped
native classes. The existing binary runtime operates on arbitrary natural
block values, so its primitive contracts apply to each class sum. Native
half preserves every other physical class and terminates by its established
unprocessed-input decrease. Ordinary primitives also terminate on every
finite admitted bank. The same counted blank producer supplies the required
all-zero class store, with a new literal startup check for each selected
complete table.

Each finite retained grammar segment therefore completes in finitely many
physical transitions. The old source search's cofinal progress is preserved,
as is its complete ordered event sequence. The unchanged B-exit adaptation,
one-step ingress shift and exact all-row event quotient preserve the
finite/infinite distinction. The source theorem still yields finitely many
marked events iff NP=coNP.

## Explicit certificate stages

1. Original allocation and contextual certificates use their original
   carrier, normally27 cells. `pre-control-grammar.json` is the contextual
   output before finite administrative control rewriting.
2. The fixed control plan ends at `pre-projection-grammar.json`, still with
   that original carrier.
3. `bank-projection.json` links it to `pre-coalescence-grammar.json`, normally
  25 cells, with omitted coordinates interpreted as zero.
4. `coalescence-invariant.json` is an identity structural certificate and a
   post-fixed invariant over this exact pre-coalescence grammar/carrier.
5. `bank-coalescence.json` records its hash, complete class partition, class
   map, physical order, native prefix, every nontrivial zero obligation,
   checked-operation count and mapped retained graph identity.
6. `grammar.json` and the complete raw/B/event tables use the new physical
   class carrier. The original logical-to-physical source map remains in
   `allocation.json`; the class map is a separate relation, not a silent
   replacement of that certificate.

`groups-411.json` preserves the first complete 411-state group plan.
`groups-407.json` preserves the selected follow-up: the bounded search
ranked252 admissible19-class partitions and generated complete tables for
twelve candidates, each measured at407 event states. The19-cell clique
bound applies only to this finite zero-partner conflict graph. Any
different plan requires admission replay and a fresh complete physical
count. Finite tests and independent reviews have their own exact-byte
bindings. This proof and the experiments establish neither a global state
minimum nor a sub-250 feasibility estimate.
