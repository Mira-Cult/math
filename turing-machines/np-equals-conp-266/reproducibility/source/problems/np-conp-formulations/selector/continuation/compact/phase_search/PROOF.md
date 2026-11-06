# Normalized-prefix source and physical composition

This is a new source theorem for `coordinator/pair_normalize.py`, SHA-256
`7d98b2beb3676f7d0e4f0d6785a5a78d4817f05f23ec38c82635a3ea4b31a039`.
It depends on the certificate-tape simulator, total unary-record decoding,
complete-prefix padding, polynomial verifier and NP-hardness construction
in [the inherited source proof](../source/PROOF.md). The acceptance function
is AST-identical to that source. It does not use the earlier forced-write
nondeterminism argument. No permanent claim identifier is allocated here.

The conventional conclusion is that the complete selected machine has
finitely many marked transitions if and only if NP = coNP, and runs forever
in either case. The independent review records, finite tests, exact row
certificates, Lean status and CI status are separate evidence.

## 1. Unchanged finite acceptance relation

Write `A(e,x,C)` for the inherited deterministic relative-direction machine
with an existential initial certificate. For a natural `b < 2^C`, its bits
are placed low first in cells −1,−2,…; the bits of `x` occupy cells 0,1,…;
all other cells are zero. The initial state is 1, the head is at zero and its
facing is positive. State zero is accepting and absorbing. At a positive
state `s` reading `z`, the selected unary record has zero-based index
`s+z−1`. A record value `a` means independently encoded write `a mod 2`, turn
`floor(a/2) mod 2`, and next state `floor(a/4)`.

Every description is interpreted, including absent and truncated records,
with a virtual zero tail. Arbitrary unaligned state windows retain the
inherited overlapping-record semantics. This source's existential choice
is the initial certificate; it is not a fresh choice coupled to each write.

The implementation enumerates `2^C−1,…,0`, rebuilds the two tape tails and
state for each attempt, and performs exactly C loop iterations. Absorption
makes final state zero equivalent to reaching zero within C transitions.
For C=0, the unique empty-certificate attempt makes no transition and fails.
The return bit therefore is exactly A. Destructive changes to the mutable
left/right tails cannot alter the master branch, input or description.

All loops in one call terminate. Constructing `2^C` uses C iterations;
certificate enumeration has `2^C` iterations; each simulated clock has C
iterations; record selection decrements a finite natural; and each run of
unary ones consumes binary digits of a finite natural. A virtual zero record
also terminates immediately. These are statements about unbounded naturals,
not host-word bounds. The counted outer search may take enormous time.

## 2. The new finite input interface

The outer search now enumerates one natural integer `i = 0,1,2,…`.
Read its low bits in consecutive pairs `(marker,payload)`. A marker one
contributes its payload bit; the first marker zero ends the prefix. Bits
above that marker are ignored by this parsing operation. A high marker one
with no explicitly stored payload contributes a virtual payload zero.

Let the resulting payload bits be `v_0,…,v_(n−1)`. Define

`N(i) = n`, and

`D(i) = 2^n + sum(v_k * 2^(n−1−k), k=0,…,n−1)`.

The source starts `scan=i,n=0,e=1`. Each complete marker-one iteration
replaces `scan` by its quotient by four, increments n, and replaces e by
`2e+payload`. Thus it returns precisely N and D. Its marker-zero exit is
finite, including `i=0`. All even integers have N=0 and D=1, regardless of
their higher bits. The higher bits remain present on the candidate's input
tape; a verifier cannot assume that they were erased by the outer parser.

The source's reference language is

`K_norm = { i : A(D(i),0,N(i)) }`.

For the old low-bit-first word convention, this is the old reference language
applied to the reversed payload. That reversal is intentional. There is no
claim that the new reference tests or outer primitive histories are identical
to the old ones.

## 3. NP membership and the explicit reduction

For a raw input word of length m, N(i) is at most `ceil(m/2)` and D(i) has
N(i)+1 bits. Parsing, reversal and constructing D take polynomial bit cost.
The inherited bounded verifier for A then proves `K_norm` is in NP: it uses
at most N certificate bits and N simulated transitions, with a description
of at most N+1 bits. Leading zeroes in the raw input word change neither
integer nor parsed prefix.

For NP-hardness, let an old reference instance have low-first bits
`y_0,…,y_(n−1)`. Set `v_k=y_(n−1−k)` and output the finite integer

`i = sum((1+2v_k) * 4^k, k=0,…,n−1)`.

Its n marked pairs are followed by a virtual zero marker. Its raw binary
length is at most 2n, and D(i) is exactly the old sentinel description
`2^n + value(Y)`. Therefore this polynomial, explicit encoding preserves
reference acceptance in both directions. The empty old word maps to i=0.
The old NP-hardness theorem already pays for the input writer, preservation
of the negative certificate tape, internal runtime/witness guards,
orientation translation, complete reachable records, and polynomial padding.
Those hypotheses are not replaced by an appeal to universality alone.

## 4. Candidate languages and coverage

The new candidate at index j is

`L_j = { i : A(j,i,(N(i)+1)^j) }`.

The same j is still both description and exponent. For each fixed j,
`(N(i)+1)^j <= (ceil(m/2)+1)^j` is polynomial in raw input length m.
A certificate of that length and the inherited deterministic simulation
give an ordinary bit-cost NP verifier for `L_j`. No polynomial-time claim is
made for the physical exhaustive acceptance call.

Suppose NP = coNP. A verifier for the complement of the old NP-complete
reference supplies a verifier for the complement of `K_norm` by parsing the
marked prefix and reversing its payload. Its work can be bounded by a fixed
polynomial in n=N(i), independent of the arbitrary ignored suffix. This last
statement requires an actual tape discipline:

1. If cell zero is zero, the initial transition accepts. This is the empty
   prefix case, whose reference always fails because its clock is zero.
2. Otherwise the verifier parses only the marked prefix. It retains or
   copies its finite payload into explicitly initialized positive workspace,
   and erases/initializes every additional positive workspace cell it will
   use. It never interprets arbitrary ignored suffix bits as an initially
   blank work tape. Polynomial sweeps, binary block coding and reversal give
   a polynomial overhead in n.
3. The negative certificate half-tape is preserved while parsing and
   preparing positive workspace. The guarded verifier reads only its
   prescribed polynomial certificate prefix, rejects malformed encodings,
   and enters an absorbing accepting or permanently nonaccepting behavior
   according to the verified result.

These are ordinary finite binary-TM constructions: any additional work
alphabet is translated into finite binary blocks and finite control in the
description, rather than added to the counted outer machine's alphabet.
They are the same input-writing, workspace-initialization and orientation
translation operations used in the inherited coverage proof. Here the
initialization condition is essential because input suffixes are real data.

Let a fixed guarded implementation need at most `c(n+1)^d` transitions and
certificate bits when n>0. Choose an integer k large enough that
`(n+1)^k >= c(n+1)^d` for every n>=1, for example
`k >= d+ceil(log2(max(c,1)))`. The complete-prefix padding theorem gives
arbitrarily large equivalent descriptions j, so choose j>=k. All reachable
rows, including overlapping windows, are complete before the padding; no
external sentinel or higher padding bit affects a reached transition.
The larger clock and certificate cannot introduce false acceptance, because
the verifier has its own guard and reads only the prescribed witness prefix.
Every useful witness extends to the longer outer certificate.

For n=0 the outer clock is exactly one for every j, including j=0. The
one-transition initial-zero wrapper therefore remains necessary. Padding
preserves that initial transition, so it works for every even i, including
those with arbitrarily large ignored suffixes. This proves that some L_j is
exactly the complement of `K_norm`.

Conversely, if any L_j is that complement, NP membership of L_j and the
NP-completeness of `K_norm` imply coNP is contained in NP. Taking complements
also gives NP contained in coNP, hence NP = coNP.

## 5. The search and the event polarity

For each j the source first beeps, then tests every natural i in increasing
order. It refutes j precisely when the candidate and reference acceptance
bits agree. The two cases are `(1,1)` (unsoundness for the complement) and
`(0,0)` (incompleteness for the complement); both are finite acceptance
computations. Inequality is agreement with the complement and continues
silently to i+1.

Every finite counterexample integer is eventually tested: all preceding
normalizations, clocks and acceptance calls terminate. A failed candidate
advances to j+1 and starts its input search again at zero. Thus every finite
candidate index is reached unless an earlier candidate has no counterexample.
The reject-everything candidate is defeated by i=0. The j=0 candidate accepts
every input in one transition; i=1 has n=1,D=2 and is reference-accepting, so
it supplies an explicit `(1,1)` refutation. Zero clocks, exponent zero,
missing records, high virtual zeroes and empty inputs remain covered by the
unchanged acceptance relation and the explicit parsing definitions.

If NP differs from coNP, each candidate has a finite counterexample, so
infinitely many candidates and infinitely many beeps occur. If NP equals
coNP, some candidate is correct; the earliest such candidate is reached
after finitely many refutations and then tests inputs forever without another
beep. At least its initial beep has occurred, but the total is finite.

The source never physically halts: successful refutations continue the
outer loop; a correct candidate performs infinitely many finite input stages.
Consequently, under the established convention, 1-acceptance (infinitely
many designated events) corresponds to NP != coNP. A finite run cannot
decide which alternative holds.

## 6. Fresh compiler and storage certificates

`build_normalized.py` compiles this exact source through the inherited
compiler and primitive contracts, using a fixed published grammar plan and
newly computed 26-logical-cell/19-physical-class storage certificates, after
projecting the original 28-cell allocated bank. The
artifact itself is authoritative about carrier sizes. The builder verifies
the contextual, control, projection and coalescence digest chain. Reproduction
does not search for another plan or register grouping.

A physical class is the sum of its logical ghost values. Each reached
operation's other class members must be zero. The new invariant, operation
occurrences and both native-HALF branch images are checked; names are never
treated as unrestricted aliases. HALF retains quotient/parity semantics.
The inherited all-zero counted bootstrap realizes the new finite layout.

The source, grammar and arithmetic proofs establish positive finite physical
segments for every admitted operation. The finite-control certificate rejects
administrative cycles, and the primitive proofs cover finite scans, shifts,
returns and scratch restoration. Their composition transfers the source's
infinite execution and event sequence; a silent physical hang cannot stand
in for a correct candidate.

## 7. New completion domain and literal selected table

The normalized source first produces a complete 395-state raw table, a
392-state B-exit table and a 391-state marked table. `build_selected.py`
derives its 13 excluded B rows from this producer's named selector requests,
fresh raw names and fresh exact quotient preimages. It checks that **every**
raw preimage of a hole is excluded. It does not reuse the old 401 completion's
numerical hole identities or plan.

Exclusion is a semantic premise, not a consequence of a row appearing in a
totalization list. The [native kernel domain proof](../compiler/native/PROOF.md)
and [shared-selector/blank composition](../native/COMPOSITION.md), with the
[named excluded-read obligations](../tape_local/completion/PROOF.md#the-thirteen-excluded-rows),
apply because the new selected runtime keeps those admitted-domain rows and
contracts unchanged. The new selector extends the native operand prefix by
one paid index; every selected block still begins with its base one and all
reserved mode pads are zero. The new maximum leaf path is 80<3822 and the
19 active fields fit the 1909 paid zero fields, so the finite blank initializer
and gap/return contracts still apply. The new source/storage certificates
establish the hypotheses at each later primitive entry. This proves the
named excluded reads cannot occur on the admitted execution; the sink then
has no reachable predecessor. The new quotient-preimage check transfers
that semantic exclusion to exactly the recorded 13 B holes.

The fixed new completion changes only those excluded rows. All 771 retained
rows preserve their writes, moves and targets under the supplied relation.
An ordinary all-row quotient then yields 388 B states; an independently
checkable ingress adaptation and all-row event quotient yield 387 marked
states. Every state has both rows, every target exists, every movement is L
or R, and no terminal or cleanup state is omitted. Start state, head position
and blank symbol are zero on a two-way all-zero tape.

The sole marked row is `112 1 0 L 1 1`. Its event precedes the companion's
B=1 exit by one step. Completion preserves complete tape/head configurations
and physical time on admitted runs of the new normalized source. Its trace
is not asserted to match the old 407/401 source, whose input enumeration is
different. The exact literal-table theorem remains a conventional composition
with finite checked certificates, not an already completed Lean theorem.
