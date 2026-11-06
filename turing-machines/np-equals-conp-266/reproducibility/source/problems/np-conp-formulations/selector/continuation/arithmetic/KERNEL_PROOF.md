# Unary record and paired-halving preservation

This is the coordinator's author proof for `record_pop.py` and
`half_kernel.py`. It is conditional on the frozen natural-register compiler's
primitive, allocation, grammar and physical-runtime contracts. The independent
kernel review and its executable fixtures are recorded separately. This is a
conventional proof, not proof-assistant certification. No permanent claim IDs
are introduced.

## Entry and representation

All registers contain finite, unbounded naturals. A register decrement has a
success continuation when its old value is positive and a failure continuation
when its old value is zero. Successful decrements subtract one. A register
increment adds one. The grammar's explicit continue returns to the named loop
before executing any later expression in its body.

The shared arithmetic bank is A, B, Q, R, C, and S is the copy scratch. At a
complete source-expression or statement boundary the arithmetic bank and S
are zero. Owned temporaries, source slots and this shared bank are disjoint.
The new half kernel needs only Q=R=0; B, C and S may contain arbitrary protected
finite values. Its body does not read or write them.

## A paired consuming half

Let the input be A=x and Q=R=0. At the head of each paired iteration after k
successful pairs the invariant is

\[
 A=x-2k\geq0,\qquad Q=k,\qquad R=0.
\]

If the first decrement fails, A=0 and the kernel returns. If it succeeds and
the second decrement fails, the previous A was one; the kernel increments R
once and returns with A=0. If both succeed, it increments Q and continues
directly to the loop head, skipping the later increment of R. This establishes
the invariant for k+1. There are at most floor(x/2) successful pairs followed
by one failed test. On return,

\[
 A=0,\quad Q=\lfloor x/2\rfloor,\quad R=x\bmod2.
\]

B, C and S are unchanged. The result is the same half contract used by the
old scalar and simultaneous quotient/remainder lowerings. The new loop avoids
resetting a temporary remainder on each pair; it introduces no wider physical
alphabet, direct binary-number operation, external interpreter or finite bound.
Its primitive count can be large but is finite for every finite input.

## Strictly recognized record block

`match_pop` recognizes exactly the following three consecutive statements,
with distinct plain names `count` and `stream`:

```python
count = 0
while stream % 2:
    count += 1
    stream //= 2
stream //= 2
```

The constants must be integers, rather than Boolean literals with equal Python
values. The while has no else branch and exactly the two indicated body
statements. Additional effects, other divisors, reordered updates, duplicate
names, augmented reset forms and nearby but different source are not matched.
All unmatched statements pass through the inherited compiler. The original
source AST and its liveness/interference analysis are unchanged.

For finite input x, let a be the number of low one bits before its first zero,
where the finite binary expansion is extended by zeros. Define

\[
 t=\left\lfloor x/2^{a+1}\right\rfloor.
\]

These are finite for every natural x, including zero and an all-one expansion.
The source block finishes with `count=a` and `stream=t`.

The emitted block first clears count. On each iteration it moves stream into
A, calls the selected half kernel, and moves Q back into stream. A and Q are
then zero. It consumes R using a conditional decrement. An odd input has R=1:
the decrement succeeds, count increases, and control continues at the loop
head. An even input has R=0: the test fails and control leaves the block.
Thus every odd iteration consumes exactly one low one and every exit consumes
the first zero. After a iterations count is a, and the last half produces t.
All arithmetic registers are restored to their boundary values. There are
exactly a+1 finite half calls, including one call for x=0. This is a terminating
decoder of the virtual-zero-tail codec, with no malformed-encoding stall.

Count and stream cannot share a physical source slot: they are simultaneous
live values in the original loop body. In particular stream is needed after
the update that reads count, and count is needed on the loop's subsequent
iteration. The frozen source allocator's interference relation therefore
separates them, even when one result dies immediately after the block. Both
are also disjoint from the shared arithmetic bank. Other source values remain
unchanged except for already permitted dead-slot reuse.

## Composition, event order and progress

The selected tuple-half rules call the same overriding half kernel and consume
its Q and R outputs before reaching a statement boundary. The record lowering
uses no source calls or event primitive. Its recognized block contains no
escaping break or continue; inherited control around the block is unaffected.
Nested surrounding loops therefore retain their control destinations.

The relation is exact at completion of the matched block, not at its removed
interior source-expression boundaries. All live source values, control
continuations and ordered source events agree. Every matched block takes
finitely many primitive steps, so replacing arbitrarily many blocks along an
infinite run preserves cofinal progress. The compiler cannot turn a finite
source check into an infinite silent physical computation through these rules.

The complete physical theorem additionally requires the source theorem,
other selected compiler rules, the certified grammar transformation, counted
blank initialization, runtime simulation, total table and event adaptation.
Those obligations are assembled in `COMPOSITION.md`; the small kernel proofs
alone are not a complete beeper construction.
