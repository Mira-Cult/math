# Relative tape with forced-write branching: source theorem

## Scope and authorship

This author proof concerns `forced_relative.py`, SHA-256
`c7bcab7ec604f443b67ae44e25b755bd7f3b09e0933e31f842758ad1f7e35f57`.
The author is the current `internal-model-reviewer` agent. The same invocation
also authors the accompanying source oracle and normalization fixtures. These
are producer evidence, not independent mathematical or implementation review.
No permanent claim IDs are introduced.

The protected 581-state source and producer remain unchanged. This source
changes the description codec and therefore the fixed reference language. It
is a new construction, not recovered historical bytes or a pointwise rewrite
of the old reference predicate. It retains that construction's own-description
bounded-blank architecture and unchanged exhaustive candidate/input controller.
The full frozen-compiler measurement is 540 raw states, 538 B-exit states, and
537 marked-transition states; composition with new compiler lowerings and
independent exact-producer review are separate obligations. No claim of
state minimality or a sub-250 bound is made.

The source theorem is:

> The source runs forever and emits finitely many `beep()` events exactly when
> NP = coNP. Every single acceptance call and every incorrect-candidate stage
> terminates in finite time. All candidate indices, exponents, inputs, and
> simulated clocks remain unbounded.

## 1. Every description defines a finite nondeterministic machine

For a natural number e, read its binary expansion from low bits to high bits,
then continue with infinitely many zero bits. Consecutive records have form
`1^a 0`, where a is a natural. Number the records starting at zero. A machine
configuration has state s, head position h, facing f in {-1,+1}, and a binary
finite-support tape. It starts in state 1, at head zero, facing +1. State zero
is accepting and absorbing. Positive states need not have aligned addresses.

In a positive state s, on scanned bit z and nondeterministic choice c in
{0,1}, select record

    r = s + 2z + c - 1.

This is nonnegative. If its value is a, let t=a mod 2 and s'=floor(a/2).
Write c at the current cell. Replace f by f'=(-1)^t f, move the head to
h+f', and enter s'. Thus the chosen branch bit is also the written symbol;
the record contains only a relative turn bit and the next state address.
Both possible choices exist in every positive state.

All descriptions have total semantics. Every field ends because the actual
bit stream is finite. Missing fields and unfinished one runs finish in the
virtual zero tail. A missing record has a=0 and accepts after writing c and
moving forward. There is no invalid-encoding wait or undefined transition.
If ell is e's bit length, every field value is at most ell, so every next
state is at most floor(ell/2). The reachable addresses are therefore contained
in `{0,...,max(1,floor(ell/2))}`. Including the two facings still gives a finite
ordinary nondeterministic machine, with only O(ell+1) states. An unaligned
address merely causes two row windows to overlap; it does not cause ambiguity
or unbounded syntax interpretation.

### Complete aligned encoding and arbitrary harmless padding

Consider any finite machine already in this relative, forced-write model,
with positive logical states q=1,...,k, start q=1, and accepting q=0. Encode
logical q>0 by address s(q)=4q-3, and encode q=0 by address zero. For q>0 its
four records have indices 4(q-1),...,4(q-1)+3, so the row blocks are disjoint.
Encode every one of the 4k rows, in order, as

    1^(turn + 2*s(next)) 0.

All used records end inside this complete prefix. Its length L is at most
32k^2: each record has length at most 8k-4. Let e0 be its low-bit integer,
retaining the specified length even when the high bits are zero. For every
Q>=0, e=e0+2^L Q has exactly the same rows on every reachable logical state,
and all those rows stay inside the encoded finite state set. Thus the
encoded machine has exactly the same execution on every initial tape, every
choice sequence, and every clock, independently of Q. In particular its
integer descriptions are arbitrarily large without changing its running time.

## 2. Universality with constant-factor time overhead

Start with an ordinary binary single-tape nondeterministic machine N, with
left/right moves, start state 1, accepting state zero, and a positive rejecting
sink. Its two choice rows may duplicate deterministic actions. Standard finite
normalization of a fixed machine removes stay moves and converts a larger
finite branching degree to binary branching, with a constant overhead. These
normalizations preserve polynomial time; they do not supply the NP=coNP theorem.

First convert N to a machine whose choice bit is always its written bit, but
whose direction remains an absolute left/right move. For each original
transition selected by (q,z,c), with desired action (w,d,q'), use three steps:

1. At the old head, choice c writes c, moves right, and enters a new relay
   state remembering the complete selected transition, including w,d,q'.
2. The relay reads neighbor bit z1. Choice z1 preserves that bit, moves left,
   and enters a commit state for the remembered transition. The other choice
   enters a permanent rejecting sink.
3. The commit state allows choice w, which writes the desired w, moves d,
   and enters q'. The other choice enters the rejecting sink.

A good three-step path changes exactly the original scanned cell and performs
exactly N's transition. The temporary first-step write is overwritten at step
three; the neighbor is restored at step two. The relay/commit states retain
all finite information needed, regardless of the symbol read at step three.
No wrong forced choice can accept because its target is a permanent sink.
Consequently every N computation corresponds to a surviving forced-write
computation with exactly three times as many steps; every accepting forced
computation is such a simulation. There are O(k) new states for k old states,
since each old state has four rows. The sink can itself write either branch
bit and move right while staying in the sink.

Next convert absolute directions to relative turns. Duplicate every positive
state q into (q,f) for f=+1,-1. A forced-write row with absolute direction d
uses turn zero when d=f and turn one otherwise, and enters (q',d) if q'>0,
or accepting state zero if q'=0. Start at (1,+1). At every reachable
configuration the control's f agrees with the actual facing. Each row writes
the same bit and makes the same absolute move as the forced-write machine.
This introduces no step overhead and at most doubles its states. Renumber
the pairs so (1,+1) is state 1, then apply the aligned encoding above.

This proves an effective polynomial-size encoding of every ordinary finite
binary nondeterministic machine in the new codec, with constant time overhead.
It is also an explicit translation usable in finite fixtures. It does not
assume that machines with a constrained write alphabet are universal without
paying their simulation control.

## 3. Source simulation and totality

During an active branch, `read` is the scanned bit. The low-to-high bits of
`right` are the cells h+f,h+2f,..., and those of `left` are h-f,h-2f,... .
The initial simultaneous assignment `read,right=right%2,right//2` establishes
this invariant from the ordinary initial tape integer, with all negative
cells blank and initial facing +1.

Each positive `steps` iteration first decrements `steps` and pops one branch
bit into `write`. The body does not read `steps`, so moving its decrement to
the head of the loop leaves the exact number of simulated transitions fixed.
Under `state>0`, the source initializes `place=r+1=state+2*read+write`.
Each positive `place` iteration first decrements it, then counts and removes
one unary record. The body does not otherwise read `place`. After the final
iteration, `state` contains exactly a_r. The simultaneous quotient/remainder
assignment extracts its turn bit and next state.

If the turn bit is one, swapping `left,right` exchanges the two tails and
reverses their semantic facing. The shared assignment `left=2*left+write`
then inserts the written old head cell behind the new head. Popping
`read,right=right%2,right//2` obtains the new scanned cell and forward tail.
This is exactly the relative transition in Section 1. For state zero no tape
operation is performed, realizing accepting absorption.

For a clock C and branch integer b, the source pops exactly C choice bits,
including after entry to state zero. Hence its final `choices` is
floor(b/2^C). The positive overflow test precedes the acceptance test. Branches
b=0,...,2^C-1 enumerate all length-C choices; if none accepts, branch 2^C
returns zero. No more than 2^C+1 branches are attempted. For C=0 the start
state remains positive: b=0 fails acceptance and b=1 returns zero on overflow.
Thus the source returns exactly bounded nondeterministic acceptance, including
the zero clock and all malformed or missing record cases.

Every branch and lookup is finite. Positive odd `digit` strictly decreases
under halving; an all-zero tail immediately ends the inner field loop.
`place` decreases once per finite record, and `steps` decreases once per
finite simulated transition. All remaining arithmetic is finite natural
arithmetic. Therefore `accept(e,initial,C)` terminates for every natural triple,
not only for aligned codes or the reduced test fixtures.

## 4. A fixed NP-complete target on every raw binary word

For a raw binary word Y of length n and low-bit integer y, define

    K = { Y : accept(2^n+y, 0, n) = 1 }.

The description includes the high sentinel bit. The tape is blank and the
clock is the raw length n. Every word has meaning, and the empty word is
outside K because its clock is zero.

K belongs to NP. Guess n branch bits and simulate n transitions of the codec.
Its description has n+1 bits. Section 1 bounds the state address and selected
record index by O(n+1). Scanning the actual description and the required virtual
zero records therefore takes polynomial time per transition. Only n tape moves
and cells in a radius n can matter. A deterministic verifier with an ordinary
binary work representation checks the witness in polynomial time. This is a
complexity bound for K, not a claim that the counted unary physical interpreter
runs quickly.

For NP hardness, fix an arbitrary language L0 in NP and a normalized recognizer
N with a known polynomial bound p(b) on its computation on the self-delimiting
input E(x)=1^b 0 x. For each b-bit x, construct an ordinary blank-start machine
D_x. A finite O(b+1)-state writer prints E(x) and returns the head to zero.
It then simulates N using time-layered control (q,t), 0<=t<=p(b), so every
branch accepts by the inner guard or enters a permanent rejecting sink. Thus
D_x accepts some branch iff x belongs to L0, and no first acceptance can occur
after the guard. Its state count, construction time, and successful running
time are polynomial in b.

Translate D_x by Section 2, paying the threefold time overhead and linear
control expansion, and encode its complete aligned prefix of length Lx.
Let T(b) bound all successful translated runs including the writer, return,
and guard. Both T(b) and Lx are polynomial in b, since the unary-action prefix
length is at most quadratic in the translated state count. Choose
n=max(Lx,T(b)). Let Y_x be that complete prefix followed by zeros to length n.
The sentinel in 2^n+y_x lies outside the complete prefix and cannot change a
used transition. If x belongs to L0, an accepting run finishes by n; otherwise
no run ever accepts because of the inner guard and permanent sink. The padded
outer clock cannot create a false acceptance. This is a polynomial-time
many-one reduction from L0 to K.

Thus K is NP-complete and its complement is coNP-complete.

## 5. Polynomial candidates and the coupled exponent

Candidate j is the language of description j on E(Y)=1^n 0 Y, under clock
(n+1)^j. For each fixed j this is in NP: its machine is finite, its input
encoding is polynomial, and the clock has a fixed polynomial degree. The
source enumerates every natural j, with no bound on the description or degree.
A correct candidate means acceptance equals the complement of K on every Y.
If one exists, the complement of K is in NP.

Conversely suppose the complement of K is in NP. Take a polynomially clocked
ordinary recognizer V for it, with an inner guard and permanent rejecting sink,
and normalize it to the forced-write absolute-direction model in Section 2.
Before the orientation translation, add a two-step input wrapper in that same
forced-write model:

- At its start, reading zero, either choice enters accepting state zero on
  the first step. This handles E(empty)=0 with clock (0+1)^j=1.
- At its start, reading one, only choice one preserves it, moves right, and
  enters a relay. Choice zero enters the rejecting sink.
- At the relay, reading z, only choice z preserves it, moves left, and enters
  V's forced-write start. The other choice enters the rejecting sink.

For every nonempty E(Y), the unique surviving wrapper restores the exact tape
and head after two steps. Orientation translation then sends that relay to
the copy of V's start with facing -1; its state records this facing, so the
next relative step still performs the intended absolute direction. No reset
of the unrecorded semantic orientation is assumed. The wrapper's read-zero
acceptance concerns valid E(Y) only; its behavior on other tape encodings is
irrelevant to candidate correctness. All other spurious branches reject.

Let g(n) be a polynomial bounding successful V simulation including this
wrapper on n>=1. Choose constants C>=1,d>=0 with g(n)<=C(n+1)^d. Any
j>=d+ceil(log2 C) satisfies (n+1)^j>=g(n) on n>=1. The complete-prefix padding
lemma supplies arbitrarily large integers j describing exactly the wrapped
machine, with unchanged behavior and running time. Choose one beyond that
degree threshold. It is correct on nonempty inputs by clock domination and
the guard, and on the empty input by the one-step wrapper. Hence a correct
candidate exists.

A correct candidate exists iff the complement of K is in NP, iff NP=coNP.
For the last implication, the complement of an NP-complete K is coNP-complete;
if it is in NP, closure under polynomial many-one reductions gives coNP subset
NP. Taking complements gives the reverse inclusion. No theorem about the
separate P=NP lane or an equiconsistency construction is used.

## 6. Exhaustion, finite refutation, and event polarity

The `main` controller is byte-for-byte the same function body as the protected
incremental source. At each comparison it maintains

    candidate = 2^n,
    candidate <= i < 2*candidate,
    initial = candidate - 1 + 2*candidate*(i-candidate).

The low n ones, then zero, then n raw bits of `initial` encode E(Y), where
i=2^n+y is the sentinel description of Y. Initially i=1,n=0,candidate=1,
initial=0. The within-length increment adds 2*candidate; the length boundary
doubles candidate, increments n, and resets initial=candidate-1. Thus every
finite raw word is visited in sentinel order, without a gap at any boundary.

The two calls return bits. Equality means the candidate disagrees with the
complement of the reference bit, so exactly that finite witness rejects it.
Unsoundness and incompleteness are both finite errors. Reject-everything fails
on the empty input. Accept-everything fails, for example, on the one-bit word
0: its sentinel code 2 has record zero equal to zero and accepts blank in one
step. A malformed description cannot evade the tests by stalling, because
Section 3 proves all calls finite.

Every incorrect j has a least finite witness. All preceding comparisons have
finite duration, including their finite power arithmetic; their finite sum is
finite. The controller reaches the witness, rejects j, increments it, and emits
a new source event. If a correct candidate exists, the least such j is reached
after finitely many rejections and its unbounded input scan then proceeds
silently forever. If none exists, each j is rejected in finite time and there
are infinitely many events. The initial event and every later one have the
same fixed designation. There is no physical-halting or finite-state-visit
interpretation of silence.

## 7. Physical composition and evidence limits

All variables are naturals. Every division/remainder uses positive literal
two. The only expression subtraction is candidate-1, with candidate>=1;
`place` and `steps` decrement only under positive guards. Tuple assignments,
including swaps and quotient/remainder pops, read all old inputs before any
output update. The call graph remains main -> accept. The fixed finite number
of source registers places no bound on their natural values, source indices,
clocks, logical machine addresses, or tape positions.

To derive the complete physical theorem, compose the source result with the
exact selected compiler's source-to-grammar refinement, primitive termination,
register/scratch invariants, counted blank initialization, complete literal
transition table and event certificates. All finite source stages then finish
in finitely many physical steps, giving cofinal progress. The B convention is
exits from the designated B state, not its entry; the event-table adaptation
moves each event to its incoming transition one step earlier, followed by an
exact event-colored quotient. Finite event-free startup preserves finite versus
infinite event count. These are implementation proof obligations for the exact
new table, not consequences of a state-count measurement alone.

Author fixtures compare the packed source with a differently structured
explicit-record sparse-tape frontier, test the three-step forced-write and
orientation translations, complete-prefix padding, the empty wrapper, boundary
clocks, truncated/missing records and incremental framing, and compare reduced
source programs with emitted grammar. They are finite regression evidence and
do not prove NP=coNP or eventual silence of the full machine. Large rejecting
length-clock descriptions need exponentially many source branches; their
abstract oracle results are not reported as completed source execution.
