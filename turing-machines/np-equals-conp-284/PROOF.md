# Proof guide for the 284-state machine

The argument has three parts. First, a search over candidate complement
verifiers has finitely many candidate changes exactly when NP = coNP.
Second, the particular reference language and candidate enumeration implement
that search with the required bit-cost bounds. Third, the exact binary table
implements the search from a blank tape without losing events or getting stuck
in administrative work.

## 1. Search for a complement verifier

Let `R(i)` be the reference acceptance bit on natural input `i`, and let
`Q(j,i)` be candidate `j`'s acceptance bit. The controller starts at candidate
0 and input 0. It emits an event when beginning a candidate. For that candidate
it tests inputs 0, 1, 2, and so on.

- If `R(i) ≠ Q(j,i)`, the candidate is right on this input and the next input
  is tested without a beep.
- If `R(i) = Q(j,i)`, the candidate is wrong. The controller advances to
  candidate `j+1`, emits its entry event, and restarts at input 0.

Every comparison finishes. Consequently, the event stream is finite exactly
when some fixed candidate complements the reference on every input. If such
a candidate exists, all earlier candidates either fail after finitely many
tests or already work forever. If none exists, every candidate eventually
fails and the events continue indefinitely.

Both equal outcomes matter. `(1,1)` gives overlapping acceptance; `(0,0)` leaves
an input accepted by neither side. Testing only the first kind would not
recognize a complement.

## 2. The actual predicates

The source parser reads a natural input in low-bit-first order. Starting with
`(N,D)=(0,1)`, each marker bit 1 consumes a following payload bit `b` and updates
`(N,D)` to `(N+1,2D+b)`. The first marker bit 0 stops the parser. All higher
input bits are ignored by the reference parser, but the candidate still
receives the entire original input. Virtual high bits are zero.

Thus `2^N ≤ D < 2^(N+1)`. Let `A(p,x,c)` denote bounded existential acceptance:
the described relative-tape program `p`, begun with input `x`, has some
certificate that reaches its absorbing accepting state within `c` simulated
steps. Only the low `c` certificate bits can affect that result. Invalid,
missing, and truncated records have the specified total decoding behavior;
timeout means rejection.

The two source predicates are

`R(i) = A(D(i),0,N(i))`

`Q(j,i) = A(j,i,(N(i)+1)^j)`.

The reference source actually searches certificates below `D(i)`, while the
candidate searches below `2^((N(i)+1)^j)`. The sentinel bound and the proved
low-bit truncation property make the former search equivalent to searching
all relevant `N(i)`-bit certificates. This is an existential search in both
phases, not a deterministic zero-certificate execution.

The program number and clock exponent are coupled: the same `j` is used for
both. When `N(i)=0`, the candidate clock is exactly one, however large `j` is.
Those are real constraints on the coverage proof, not implementation details
that can be replaced by an independently chosen exponent or a larger clock.

## 3. Connection to standard complexity classes

For the complexity statements, raw Boolean lists are interpreted as
little-endian natural numbers, allowing redundant high zeroes. The reference
and each fixed candidate are total languages on all those lists. There is no
unstated promise that an input has a particular frame or suffix.

The formalization proves four ingredients:

1. The reference language belongs to canonical NP. Parsing, record lookup,
   bounded simulation, witness guards, and encoding costs are paid in the
   pinned machine-time model.
2. SAT has a polynomial many-one reduction to that reference, making it
   NP-complete under the established canonical SAT theorem.
3. For each fixed `j`, its candidate language belongs to canonical NP. The
   exponent may depend on that fixed candidate, as ordinary NP membership
   permits; it does not vary with the input.
4. If the reference complement belongs to NP, one fixed enumerated `j`
   agrees with it on **every** input.

For the fourth ingredient, a verifier is compiled to the source's finite
program convention. An explicit wrapper handles the one-step empty-prefix
case. Positive-prefix execution pays its two entry turns and polynomial time
and witness bounds. Acceptance-preserving description padding then makes the
same program number large enough to serve as the needed exponent. The result
covers arbitrary high suffixes and one fixed candidate, rather than selecting
a new verifier separately for each input.

If a candidate complements the reference, its NP membership puts the
reference complement in NP. NP-completeness then gives NP = coNP. Conversely,
NP = coNP puts the reference complement in NP, and coverage supplies a good
candidate. Combining this with the search argument proves the equivalence
for the checked register graph.

## 4. From the register graph to the binary tape

The intermediate graph has 185 control positions and twelve natural-valued
register classes. Those are a proof model, not a different state-count claim
for the binary machine. The literal table includes the controller,
initialization, register representation, selectors, scans, return paths and
event handling.

The physical invariant connects the graph control position and register bank
to the actual tape, head and parser boundary. It covers the ordinary operation
cases, zero/odd/even native halving, the special root, and the beep. Each graph
step is realized by a **positive finite** sequence of literal transitions,
with exactly the same emitted event word and a restored invariant.

Induction gives a matching physical execution for every finite graph prefix.
Its duration is at least the number of graph steps. The proof separately
starts at the literal all-zero tape, preserves the required infinite blank
ray through the bootstrap, and carries the first beep into an aligned active
window. No prepared tape or reachable-window premise is left to the caller.

This produces exact event-prefix matches at arbitrarily late graph and
physical times. A stream is eventually silent precisely when the lengths of
all its finite emitted prefixes are bounded. The cofinal matches transfer
that boundedness both ways. This argument controls the complete late event
stream; it does not infer an infinite-run property from a finite replay.

Finally the parser-binding theorem identifies the checked machine with the
literal table text supplied in this package. The resulting endpoint is the
284-state marked-table equivalence stated in the [README](README.md).

## What the result does not say

It does not decide NP versus coNP, prove P = NP, bound the time until the last
beep by a computable test of silence, establish state minimality, or certify
the smaller 266-state table. The 285-state exit-from-B companion uses a
different observer and is separately documented. The provenance and scope of
kernel checking and nonauthor review are in [VERIFICATION.md](VERIFICATION.md).
