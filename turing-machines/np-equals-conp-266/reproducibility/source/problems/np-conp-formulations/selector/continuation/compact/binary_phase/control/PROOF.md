# Ordinal reuse and direct native parity control

This is the source and lowering proof for `build.py --case direct-branches`.
It is an acceptance-equivalent replacement for the frozen normalized-prefix
source, not a claim of identical source or physical traces. No permanent claim
ID is introduced. The endpoint remains the theorem in
[the normalized-prefix source proof](../../phase_search/PROOF.md), using the
[inherited acceptance model](../../source/PROOF.md).

The independently counted complete parent has 374 marked states and a
375-state B-exit companion. A later excluded-row completion, if supplied, is
separately proved and bound; no historical numerical hole list is used here.

## 1. Source contract and unchanged outer search

The frozen control is `../../phase_search/coordinator/pair_normalize.py`,
SHA-256 `7d98b2beb3676f7d0e4f0d6785a5a78d4817f05f23ec38c82635a3ea4b31a039`.
The new source `source_direct_branches.py` has SHA-256
`3209d74668903ca99a3dcd60343be3b9ddde61ee9b2b226019eb1d3bcc9f4840`.
Its entire `main` AST is unchanged. Consequently it still normalizes all
finite input integers by low-first marker/payload pairs, builds the reversed
sentinel description, compares `A(D(i),0,N(i))` with
`A(j,i,(N(i)+1)^j)`, refutes a candidate on **equal** returned bits in either
case, silently increments the input on unequal bits, and starts every candidate
with exactly one source event.

In particular the existing normalized theorem's obligations about arbitrary
ignored positive suffix bits, initialized positive workspace, preserved
negative certificate tape, virtual zero payloads, every even input, the
one-transition empty-prefix wrapper, exponent zero, complete-prefix padding,
and internal witness/runtime guards are unchanged. This construction does not
replace the independent-write certificate model by the older forced-write
branching model. The description and exponent remain coupled in `j`.

For every natural triple `(e,initial,clock)`, the new `accept` returns the same
bit as the frozen `accept`. Sections 2 and 3 prove this. Every finite acceptance
call terminates for the same reason as before: there are exactly `2^clock`
certificate attempts, each with exactly `clock` ticks, all record scans are
finite, and every arithmetic operation is over finite naturals. `clock=0`
still tries the unique empty certificate with initial state one, so returns
zero. State zero remains absorbingly accepted by the unchanged outer `if
state` guard. No clock, acceptance, reset, certificate-enumeration, or result
branch is removed.

## 2. Consume the selector rather than repeatedly count discarded records

Let the state at a simulated step be `s>0`, and let the observed bit be `z`.
The selected record has zero-based index `s+z-1`. Define `pop(d)=(a,d')` by
consuming the low run `1^a` and its first following zero, with the virtual zero
tail used when the finite integer's bits end. This definition covers zero,
all-one finite descriptions, missing and truncated records, and repeated
lookups into overlapping windows.

The frozen implementation copies `e` to `digit`, sets `place=s+z`, then repeats
`place` times: clear the state accumulator, pop a record into it, and retain
the remaining description. Only the final accumulator is used. The new
implementation copies `e` to `digit`, adds `z` directly to `state`, subtracts
one, and uses the resulting nonnegative `k=s+z-1` as a decrementing selector.
Each of its first `k` iterations skips one record without counting its run.
On termination `state=0`, and the normal final record-pop loop computes the
selected record's value in that same cell.

Induction on the number of skipped records gives the same description suffix
as the frozen loop after its corresponding iteration. After `k` skips, both
implementations pop the same final record. They therefore produce the same
record value and final description suffix. The subtraction by one never
underflows: `s>=1` and `z` is zero or one. The decrementing selector's loop
always subtracts from a positive value. The explicit `state=0` before final
pop retains the original reset contract and is eligible for contextual
elimination only under the fresh zero-entry certificate.

For a finite stream `d`, each successful odd half removes one low one bit.
The first even half consumes the zero terminator. There are at most
`bit_length(d)+1` halves, including the virtual zero at exhaustion. The zero
stream fails immediately and remains zero. Thus a skipped ordinal is a
positive finite action on every natural input, not only on well-formed machine
descriptions. Repeating this for a finite selector is also finite.

## 3. Direct read and direction branches

Instead of assigning `read,right = right%2,right//2` and adding the transient
`read` to the selector, the new source increments the state exactly when
`right%2` is one and then divides `right` by two. These operations give the same
new state and right tail for every natural right tail.

After decoding a record value `a`, write remains independently `a%2` and the
state becomes `floor(a/2)`. The new direction branch swaps left and right
exactly when that latter value is odd, then divides it by two. Hence the next
state is `floor(a/4)`, the turn bit is `floor(a/2)%2`, and the final update
`left=2*left+write` is unchanged. A write-zero instruction stays distinct from
a write-one instruction. No disjoint-pair assumption is made about the
selected records: the index remains `s+z-1`.

This is equality of decoded simulated configurations at the end of each
simulated step. Induction over ticks and certificate attempts proves equality
of returned acceptance bits. The source's administrative operations and the
literal event times change; only the ordered candidate events are transported.

## 4. New lowering rules use only the inherited primitives

`build_skip.py` adds two guarded AST rules when `fused=False`, which is the
selected producer. It does not add a new physical opcode, marker, register-bank
ABI, return tag, or tape symbol. The native HALF operation is exactly the
[proved paid kernel](../../compiler/native/PROOF.md): it replaces `x` by
`floor(x/2)` and takes success iff old `x` was odd. Its finite suffix shifts,
reserve growth, selectors, preparation and return paths are counted.

**Skip-record rule.** The matcher accepts exactly a `while x%2` whose sole
body is `x//=2`, immediately followed by `x//=2`, with the same variable and
literal two. It emits a labelled loop consisting of HALF on `x`, continuing
only on success. Every success consumes a one, and the final failure consumes
the required zero. Section 2 gives the all-natural postcondition and finite
termination argument. There are no other variable writes or events.

**Parity-branch rule.** The matcher accepts `if x%2: body; x//=2` only when
`body` does not read or write `x` and contains no call, return, break, or
continue. The selected uses have no else body; a nonempty else is rejected
rather than silently compiled. It emits HALF on `x`, followed by `body` on
success. Since body is independent of `x`, moving the division before body
preserves every output value and the chosen branch. The syntactic prohibition
on calls also prohibits introducing an event in the reordered segment.

Both rules are compositions of already admitted HALF, INC/DECNZ and inherited
lexical control. Their source boundary realization is positive and finite.
No boolean result cell is installed merely to test and erase it afterward.
The complete build includes both acceptance callers, their masters, resets,
clock/certificate arithmetic, outer parsing/search, initialization, dispatch,
event adaptation and totalization.

## 5. Allocation and intermediate ownership

Allocation is regenerated from this changed source. The selected chain is
27 allocated registers, 25 projected logical registers, and 18 physical
class-sum registers. The fixed groups are verified against the fresh native
abstract analysis; they are not the old 28/26/19 mapping reused by fiat.

The skip rule has exactly the old stream lifetime and modifies only that
stream. For parity-branch, `x` is used by the division after the source branch,
so it is live through that branch. Every branch destination therefore
interferes with `x` in the original source CFG. Reordering HALF before the
branch does not require a new alias permission. The new rules do not install
any result before its original lifetime.

In particular the selected source allocator legally puts `accept.digit` and
`accept.write` in the same allocated slot. The selected lowering consumes
all needed description bits **before** the ordinary final write-bit result
is installed. There is no early clear of write. This exact distinction is
checked by actual-acceptance fixtures in which the alias is present.

The per-operation coalescence certificate subsequently proves every peer
zero when an INC, DECNZ or HALF acts on a class. Its represented physical value
is the sum of the ghost values. Projection certifies omitted registers zero;
control certificates relate the exact grammars before and after contraction.
Each named operation still has its original single-operand physical contract.
No arbitrary multi-operand aliasing follows from these certificates.

## 6. Physical composition and events

The admitted physical boundary consists of the inherited unary bank,
prepared control path, finite reserve, zero scratch conditions and decoded
class sums specified by the frozen compiler/runtime proofs. Each new source
segment lowers to a finite list or a finitely terminating loop of those
primitives. Primitive completion returns to the admitted boundary, preserving
all other live masters and paid scratch obligations. Finite iterations of
finite segments give finite realization of every source action. Thus no
administrative-only scan, clock or cleanup cycle can create false eventual
silence.

The compiler emits both rows for every raw state, exact full-row quotients,
and a B-exit companion. Ingress event adaptation marks the transition entering
B, one physical transition before B's exit. Its complete quotient is checked
with the fresh event map; old numerical event identities are never reused.
The source emits infinitely many events iff every candidate has a finite
refutation, and emits finitely many iff one candidate is a true complement.
The normalized source theorem therefore gives finite designated events iff
NP=coNP. In both cases the ordinary binary single-tape blank-start machine
runs forever. Infinite events retain the established 1-acceptance polarity
NP != coNP.

The fixed producer here totalizes all explicit missing rows; it credits no
missing row as a saving. Any subsequent completion must prove the excluded
named domains, check every new raw preimage, and bind its own table hashes.

## 7. Rejected and losing four-phase experiments

The first four-phase run-length decoder attempted to keep the residue modulo
four in its control path, count only the next-state quotient, and eliminate
two later HALF calls. It produced a literal 353-state table, but cleared the
write result before consuming digit. The source allocator aliases those two
cells, so the implementation was invalid. It is preserved under
`rejected353/` as a rejected complete artifact, never as a proved or reviewed
NP=coNP machine. The generator's overwritten working file is separately
labelled a matching-hash reconstruction. A fixture where digit remains live
prevents the alias and cannot expose this error; actual acceptance fixtures
are required as well.

Four repairs were completely compiled and retained: deferred output clear at
all four residue terminals (388 marked), shared parity terminals (391), an
explicit lifetime extension protecting early clear (389), and fusing the
following tail push to hold the write bit solely in control (390). Their paid
costs erase the apparent reduction. They do not alter the selected 374 parent.
Their exact source refinements, introduced lifetime constraints or output
liveness guards are separate from the selected two-rule proof above. Unless
separately reviewed, they remain author experiments, not independently
certified endpoint successors.

## 8. Evidence limits and formal handoff

`check_source.py` compares against an independent sparse-tape oracle with a
signed head, relative facing and a string-based record decoder; it also tests
source values and every-step ghost/class sums on record fixtures and actual
compiled acceptance calls. These finite tests supplement the general
arguments above. Root binary review, nonauthor mathematical review, actual
blank execution, repository integrity, remote CI and Lean certification are
separate evidence categories. No finite replay decides eventual silence.

A Lean adapter may reuse the normalized source theorem after proving
`forall e i c, accept_new(e,i,c)=accept_frozen(e,i,c)` by the record-skip
induction and read/direction identities in Sections 2–3. The physical interface
needs finite positive segment realizations for the two guarded lowering rules,
then the existing native-half, source-CFG allocation, contextual contraction,
projection, class-sum and event-map contracts bound to the new literal table.
The shared existential theorem alone does not identify these bytes.
