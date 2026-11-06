# Carried overlapping-record address and whole action

This is an author proof for the complete constructions in `experiments.json`.
It is a transfer of a local architecture from the P=NP donor, with an explicit
NP-specific source relation. The inherited normalized source theorem and
physical ABI remain the ones identified by
[the reviewed360 construction](../../binary_phase/PROOF.md). No independent
review of these changed tables is inferred from either predecessor.

## Source relation on all finite arguments

Let `A(e,i,C)` denote the selected independent-write, relative-direction
machine with existential initial negative certificate and at most `C` source
transitions. State zero accepts absorbingly; initial state is one, positive
facing, input on cells0,1,... and certificate on cells-1,-2,... . The record
selected at genuine state `q>0` reading `b` has zero-based index `q+b-1`.
These overlapping windows are essential. They differ from the donor's
`q+2b+choice-1` index.

The original two-stack acceptance source removes the low bit of the right
stack immediately before lookup. This construction removes it at attempt
initialization or at the preceding continuing transition instead. At each
new step boundary its relation is

* `left` is the same backward tape stack;
* `right` is the forward stack after removing the current read bit `b`;
* `state` holds `q-1+b`, for a genuine state `q>=1`;
* the remaining clock, certificate master/countdown, full initial input and
  description agree.

The address need not separately recover `q` and `b`: the source lookup uses
only their sum `q-1+b`, and the genuine state was already proved positive at
the preceding boundary. In particular stored zero is a valid continuing
address, not an acceptance test. Initialization starts at genuine state1 and
sets the address to the old input parity while halving the input stack once.

The ordinal countdown skips exactly this many complete records, consuming
each leading run of ones and its zero terminator. The selected final record
is decoded by a paid zero reset of `write,direction,state`, followed by binary
carry. After `r` consumed one bits,

    write = r mod2,
    direction = floor(r/2) mod2,
    state = floor(r/4).

The low Boolean is consumed by DECNZ. Its positive branch consumes the high
Boolean; positive high increments the quotient, zero high becomes one. A zero
low becomes one. This proves the invariant by the four possible residues.
The final even native HALF consumes the terminating zero. For a finite stream
`D`, the residual is `D >> (r+1)`, including `D=0` and a finite all-ones stream
whose terminating zero is virtual. No truncation or missing record is treated
as an error or an alternative transition rule.

Write `W,T,S` for those decoded values. Put `(U,V)=(left,right)` if `T=0` and
`(U,V)=(right,left)` otherwise. The complete action forms

    left' = 2U+W.

For `S>0`, it first consumes one unit from `S`, then halves `V`, adding one to
the stored address exactly when the old `V` was odd. It reaches

    right' = floor(V/2),  address' = S-1+(V mod2).

This reestablishes the next-step relation for genuine state `S`. The decoded
state test precedes parity addition, so a one read bit cannot turn HALT into
a continuing state. Conversely decoded state1 continues with address0 when
the next read is zero. Every write is its independently decoded `W`; no
forced-write assumption is introduced.

For `S=0`, the complete action source returns acceptance immediately. The
old selected source spends its remaining finite clock with absorbing state0,
then returns the same bit. Removing that event-free finite delay preserves
every acceptance value. A HALT on the final allowed transition still accepts.
For `C=0`, the unique empty-certificate attempt performs no represented step
and fails. The initial finite prehalf changes only dead work and cannot cause
acceptance. Both variants enumerate the same descending `C`-bit certificate
words, preserving the integer countdown independently of overwritten working
tape. The initial `2^C` builder remains paid in these experiments.

The early-HALT variant tests `S` before changing the tape. On zero it clears
the two Boolean flags and returns1 without the dead terminal write/turn.
That variant claims only the acceptance-value relation on this exit. All
continuing tape states and both initial certificate/input masters still agree.

The main AST is unchanged for `source.py` and `source_early.py`. Thus both
reference `A(D(i),0,N(i))` and candidate `A(j,i,(N(i)+1)^j)` results are
preserved, including both equal-bit refutations and both unequal-bit quiet
continuations. The full candidate input, including every ignored high suffix,
is still copied to its working input; the negative certificate remains intact
through preparation. `source_clock.py` only hoists the event-free exact
candidate-clock assignment before the two finite calls. Its closed lowering
is proved separately in [the clock contract](../control/PROOF.md).

The normalized input/padding/complement-verifier coverage, ordinary bit-cost
membership and coupled description/exponent argument are inherited without
alteration. The acceptance return values, outer comparison order and source
event sequence are the same; dead slots and administrative timings need not
be equal.

## Whole action lowering and simultaneous ownership

`region.py` admits the exact paid reset/carry/swap/double/append/next-state
region. It requires six distinct logical source operands. The continuing
clause is exactly decrement-one, parity-add-one, half. The retained HALT body
cannot inspect stream, flags, decoded state or tape values. In the shared
function experiment it is literally `return 1`; a different actual caller
body requires its own composed source proof. The early matcher admits the
same region inside the positive-state branch and requires an explicit two-flag
zero reset in the zero-state branch. Damaged or approximate source expressions
are not silently accepted as this operation.

Let arithmetic work `A` and ordinary scratch be zero at entry. These are
logical zero premises from the inherited arithmetic boundary invariant and
fresh global abstract analysis, not claims based merely on temporary names.
The paid source reset restores its own arithmetic scratch; the record carry
does not use `A`. The following ordinary operations implement the action:

1. Consume Boolean direction. If it was one, move `left` into `A`, `right`
   into the now-zero `left`, then `A` into the now-zero `right`. This passes
   `(0,L,R)->(L,0,R)->(L,R,0)->(0,R,L)` in coordinates `(A,left,right)`.
2. Decrement `left` to zero, adding two to `A` per unit; move `A` back into
   `left`. This leaves `left` doubled and `A=0`.
3. Consume Boolean write; increment `left` if it was one.
4. Consume/test natural decoded state. Positive uses the existing native
   right-half, conditionally increments the address and reaches a real local
   join. Zero executes the retained HALT body.

All ordinary moves here are complete DECNZ/INC loops. There is no atomic move
that could conceal simultaneous operands from the old single-operation
zero-peer checker. The early comparison changes the order of steps1-3 only
under the positive-state guard; its zero branch pays both Boolean decrements.
Neither construction uses the donor's rejected empty-half return shortcut.

Every source allocation, finite-control plan, projection and sharing map is
new. Source tuple reset order is retained. Physical cells represent sums of
logical ghost carriers; every reached INC, DECNZ and native HALF checks that
all other ghosts sharing its cell are zero. At each intermediate swap or
doubling operation the same obligation applies. This permits reuse of action
work after consuming direction only when the actual graph proves that peer
zero. Old donor or NP class-sum certificates license no new alias by themselves.
The selected carry/action arguments are unbounded naturals, and all unrelated
live masters are preserved at their exposed source boundaries.

## Finite realization, complete tables and evidence limits

Every skipped record loop strictly decreases the finite stream whenever it
continues. Every ordinal loop decreases its natural countdown. The selected
record loop also decreases the stream. Each swap/move/doubling loop decreases
a finite source operand; native HALF and its paid selection/return path have
the inherited finite realization. Each attempt consumes at most `C` ticks,
and at most `2^C` attempts occur. The unchanged normalized parser, exact clock
and finite outer updates terminate. The closed borrowed clock restores its
exponent and all work before either acceptance call.

Fresh contextual/control certificates preserve retained primitive order and
reject administrative-only cycles. Grouping finite administrative work with
the next retained primitive gives positive finite physical segments. Infinite
correct comparisons therefore remain cofinal in physical time; silence cannot
arise from a stuck cleanup or a stalled clock. Each complete table includes
the unchanged blank-start initializer and both rows at every state, with every
target present. Its own raw/B and event quotient maps define its own event
row; no numerical donor identity is transferred.

Composing these obligations with the inherited normalized source theorem gives
finite designated events iff NP=coNP, and infinitely many events/1-acceptance
iff NP differs from coNP. The physical blank run is infinite in both cases.
This is a conventional author argument. The retained fixtures support it but
do not replace it. No new blank replay, independent acceptance, external
certification or table-specific Lean result is asserted for these losing
complete experiments. The new source adapter and primitive-segment obligations
would be required in a future kernel port.
