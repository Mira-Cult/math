# Paid native half/parity primitive

This proof concerns the complete native continuation in this directory.
It preserves the frozen source `../../source/certificate_popfirst_power.py`
and its NP=coNP theorem. It changes three source lowerings, extends the
zero-entry abstract analysis with the true new primitive, and adds a paid
physical operation to the binary unary-register engine. The preceding
446-state machine and all of its producer bytes remain unchanged.

The new primitive on an unbounded natural register x is

    x := floor(x/2); take the successful conditional return iff old x is odd.

The operation name ends in `.decnz` only to reuse the inherited *conditional
control-path encoding*. It does **not** decrement the underlying register.
Its `$native-half:` tag is interpreted by the new analyzer, no-search
checker, native grammar interpreter, and physical runtime. Treating it as
an ordinary decrement in the old abstract analyzer would be unsound.

## Unary representation and literal suffix shift

An active natural x occupies a nonempty block `1^(x+1)`, separated from its
neighbors by one zero. A finite bank is followed by zeros. Before the bank
are the inherited control path, a prepared gap, a separator, and a dummy
nonempty block. Other active registers and arbitrarily many zero-valued
reserve blocks may occur to either side of the selected block.

The four `scan_1`, `scan_2`, `shift_1`, `shift_2` states used by the native
operation have the literal rows of the inherited decrement suffix shift,
with different return destinations. A forward scan begins strictly to the
right of a zero gap. In that scanned suffix there are only nonempty unary
blocks and single separators, followed by a first double zero. The scan
therefore terminates. Its backward sweep moves each separator one cell
left until reaching the designated double-zero gap. The old active suffix
is translated left by one cell without changing any of its values. At the
right edge one extra `10` zero-register block is formed. A direct induction
over the visited separators proves this full-tape relation; nothing to the
left of the gap changes. Each sweep is finite.

The extra reserve block is part of the exact physical postcondition.
Claiming that the finite bank merely shrinks by one would be false for
these inherited rows. Additional trailing zero registers do not change
any active register value and remain usable by future engine operations.

## In-place half algorithm

The entry head is at the first one of the selected `1^(n+1)` block. If the
next cell is zero, n=0: the tape is unchanged and the operation takes the
failed conditional return. Otherwise keep that first value unit as a
temporary quotient increment and move to `first`. This is exactly the
configuration obtained by splitting the block immediately after its base
unit and performing the first `boundary` step below. The implementation
avoids an erase/restore detour here.

At an ordinary `boundary` entry the selected region has the form

    1^a 0 1^m 0

with the head on the middle separator, `a >= 1`, and
`n = 2(a-1) + m + 1`. The first block is the tentative quotient prefix;
the second is the unprocessed suffix. Its zero delimiter is still the
original selected register's delimiter, translated by earlier shifts.
The operation fills the boundary zero with one, increasing the quotient
prefix by one, and examines the next two input units.

* If m=0, `first` sees zero. `undo` reverses the tentative increment and
  invokes the inherited suffix shift on the two adjacent zeros. This leaves
  a single block with value `a-1 = floor(n/2)` and takes the successful
  return, because `n=2(a-1)+1` is odd.
* If m=1, the first remaining one becomes zero and `second` sees the final
  zero delimiter. The even-return suffix shift removes the resulting gap.
  The tentative quotient increment is retained, giving value
  `a = floor(n/2)`, and the failed return is taken because `n=2a` is even.
* If m>=2, the first two remaining ones become zeros. The first is the new
  quotient/input boundary and the second is a gap. The cycle suffix shift
  removes that gap and leaves `1^(a+1) 0 1^(m-2) 0`. This reestablishes the
  invariant with a increased by one and m decreased by two. When m-2=0,
  its return head already identifies the final two-zero gap; the literal
  `cycle.return` zero row directly performs the same odd final cleanup,
  omitting an increment immediately followed by its undo.

Each cycle strictly decreases the finite unprocessed suffix by two.
Thus every call terminates, and the number of suffix shifts is exactly
`ceil(n/2)`. The full tape postcondition is: the selected original register
has value `floor(n/2)`, every other original register preserves its value,
and exactly `ceil(n/2)` zero reserve blocks append. The prefix to the left
of the selected block is unchanged. The return is `6.break.0` for odd n
and `6.break.1` for even n, with the inherited return head position.
The 15 new kernel states use only binary writes and left/right moves.
There is no scratch register, oracle, supplied input, or fixed-width bound.

## Paid selector and finite bank permutation

The native operation has a separate selector for precisely its finite set
of operand cells. Those cells are put first in the physical bank by a
recorded permutation after source-liveness allocation. The permutation
does not identify or delete any register. Each existing INC/DECNZ entry
and index row is regenerated with its new block index; logical grammar
register names and the interference certificate are unchanged. The map is
checked as a bijection on the full allocated register inventory.

The native selector uses the old, single-separator preparation ABI. Its
zero entry writes the preparation marker and enters its one paid preparation
state, which joins the inherited `1b.reg.prep_2`. On the prepared second
visit it clears the marker and follows a finite unary index chain directly
to the selected first one. No INC/DECNZ mode needs storing or retrieving.
The native return therefore joins the unchanged old engine return routines
with exactly their required two-zero header. The shared two-separator
INC/DECNZ selector and its separately preserved bootstrap aliases are
unchanged. The common dispatcher can traverse the shorter native preparation;
its longer counted bound still reaches the blank left margin before scanning
back to the same root sentinel.

The published blank initializer creates the same all-zero bank regardless
of this finite register permutation. Its concrete state numbering and table
have changed, so a new full literal blank-entry run is required and recorded
separately. The selected program's finite register inventory and maximum
path remain below the initializer's paid capacities. Registers themselves
remain unbounded. Every selector, return, shift and preparation scan has a
finite delimiter supplied by these representation invariants.

## Source lowering and source-CFG allocation

For `r, x = x % 2, x // 2`, with distinct simultaneous destinations, clear r
then apply the native conditional to x and increment r on its successful
branch. The result is exactly the original quotient/remainder pair. The
original source-CFG destination clique ensures r and x do not alias.

For the exact unary-record triple `count=0; while stream%2: count+=1;
stream//=2; stream//=2`, clear count then repeat the native conditional
on stream, incrementing count for each odd success. The final even failure
consumes the zero delimiter. If the finite bit string is exhausted, zero
still fails and stays zero, giving the same virtual-zero-tail semantics.
The emitted count and remaining suffix are exactly the inherited decoder's.

The generic shared half kernel also has a native implementation: apply half
to A, increment R on an odd success, and move A's quotient into initially
zero Q. This leaves A zero, Q the quotient and R the remainder, preserving
B/C/copy scratch. It supports reduced fixtures and any surviving ordinary
half expression without silently relying only on the selected source.

The old source-liveness allocator reads the original source CFG, independent
of the primitive's arithmetic meaning. During its *name-renaming pass only*,
native operand tags are temporarily removed so the actual source register
name is looked up in the existing allocation map. Every exact sequence
position and original operand name is recorded; the tag is restored using
the mapped physical name immediately afterwards. No semantic analysis or
control factoring runs on this temporary representation. The native operand
set is remapped in the same way, and the bank permutation is then installed.

## Extended zero-entry certificate and control optimization

The three abstract classes are zero, one, and at least two, as before.
For native half, zero has only an even edge with zero output; one has only
an odd edge with zero output; an input at least two can take either edge
and on that edge has an output that is one or at least two. These images
are exact unions for their respective classes. `abstract_half.py` uses
these transfer rules in its monotone finite fixed-point computation.

`check_contextual.py` is a new producer checker extending the frozen
structural checker. It replays every supplied abstract edge using explicit
representatives 0,1,2,3,4,5, which give all possible class/parity images.
The old zero-test rewrite is safe for a native invocation proven zero:
the call leaves its value zero, emits nothing, terminates, and takes the
failed return. All finite structural rewrite checks are otherwise unchanged.
The native certificate schema and checker are explicit; the unchanged old
checker is not represented as having accepted new primitive semantics.

After this pass, the recorded finite-control plan preserves the complete
ordered retained primitive graph, including both outcomes of every native
conditional. It rejects every jump-only administrative cycle. Interpreting
the native tags by the contract above therefore yields the same values,
events and cofinal progress as the pre-control grammar, with different
finite administrative timings. The contextual certificate binds the
pre-control grammar; the fresh control plan binds that grammar to the final
one. No plan from another source or producer is reused by state count alone.

## Full-machine event theorem and evidence boundary

The same source candidate search, its fixed coNP-complete target, finite
counterexample checks, clocks, enumeration and theorem remain in force.
Each new native primitive terminates on every finite admitted bank. Hence
each finite source stage still completes in finitely many physical steps;
there is no merely conditional statement about checkpoints if reached.
The native operation introduces no marked events. Source event order is
unchanged, and the counted B-exit adaptation plus one-step ingress shift
and exact all-row event quotient preserve finite versus infinite events.
Consequently this complete binary blank-start machine emits finitely many
marked transitions iff NP=coNP, assuming the independently reviewed source
and inherited compiler/runtime contracts linked by the selected composition.

`check_native.py` is producer-authored differential evidence, not independent
review. The independent local kernel and integrated physical audits under
`../../review/native_source_scope/` bind their own exact inputs and limits.
Finite fixtures, exact finite certificate replay, mathematical proofs, full
literal startup runs, independent review and remote CI are separate results.
No finite quiet run resolves NP versus coNP, and no global minimum or sub-250
feasibility estimate follows from this construction.
