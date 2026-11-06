# Preservation for the shared-selector NP = coNP producer

## Scope and dependencies

This is a conventional mathematical composition argument for the complete
819-state B-exit machine and its 818-state marked-transition quotient. It is
not proof-assistant certification. Source and runtime proof, independent
review, finite test evidence, and exact finite certificate checking remain
separate obligations. Review bindings and the actual finite initialization
certificate are recorded by the coordinator after the producer is frozen.

The mathematical source is unchanged: `source.py`, SHA-256
`ae23de7359cefdd34c139e59418c54e26eddf9e207b9122cfb3473d0f52a380a`.
The inherited NP = coNP proof is the
[source-preservation argument](../dictionary/optimization/SOURCE_PROOF.md),
continuation composition (historical reference: `../dictionary/CONTINUATION.md`; outside this selected-only export), and its explicitly
named PR43 language, polynomial-clock, coverage and bounded-simulation proofs.
No Horn or P = NP characterization is used here.

The generic compiler continuation was recovered from the accessible local Git
commit `b79b23a76ce7463d8e4cb211060db71e6d6d1d1f` of the P = NP lane. Its remote
publication was not established. The exact generic code and necessary original
license are copied here; [provenance.json](provenance.json) binds every byte to
its original Git blob and full local revision. This transfer does not modify
that lane. The old compiler proofs are copied byte for byte as `.md.txt`
archives so their original relative references and historical claims remain
identifiable without being presented as current package links. The following
are the proof dependencies actually used:

- [Natural compiler and physical runtime](proof-dependencies/proofs__COMPILER_PROOF.md.txt).
- [Dictionary arithmetic](proof-dependencies/proofs__dictionary-compression.md.txt).
- [Conservative liveness, positive divisors and arithmetic intrinsics](proof-dependencies/proofs__frontier-compression.md.txt).
- [Compact equality, division, consuming quotient/remainder and closed-sequence sharing](proof-dependencies/compression__grammar__PROOF.md.txt).
- [Horner assignment fusion](proof-dependencies/compression__grammar__HORNER.md.txt)
  and [countdown-loop lowering](proof-dependencies/compression__native__COUNTDOWN.md.txt).
- [Shared physical register selector and its separate bootstrap adapter](proof-dependencies/compression__compiler__SHARED_SELECTOR.md.txt).
- [Zero-entry grammar transformation](proof-dependencies/compression__compiler__CONTEXTUAL_TREE.md.txt).

The archived Horn source-applicability document is historical comparison only.
Its P = NP conclusion and its source-specific hypotheses are not imported.
The contextual *physical* quotient is retained for measured comparisons, but
is not selected: it gives no further state reduction on the 819-state parent.
The final selected quotient checks every raw physical row. The zero-entry
*grammar* transformation is selected and its narrower domain remains essential.

## Applicability to the unchanged NP = coNP source

The call graph consists of `main` calling `instance` and `accept`; neither
callee calls another source procedure. It is acyclic. All returns have their
fixed scalar or triple arity. The source compiler checks arities, supported
syntax, definite assignment and frame use. The main entry has no arguments
and never returns. The arithmetic language uses unbounded naturals; source
values here satisfy the conditions under which its saturating subtraction
agrees with the intended nonnegative arithmetic.

In `accept`, the input, clock and candidate code are arbitrary finite naturals.
The trailing-one header loop ends after finitely many halvings. Its radix is
`4*(m+3)`, hence at least 12. The simulated working-state address is evaluated
only when `state//2` is positive, so `state-2` is nonnegative. Every simulated
step decreases the finite clock. The outer branch counter exhausts the finite
branch choices, including clock zero, and the source's sentinel test ends the
call. `instance` uses finite halvings and the positive power `2**length`.
Its malformed-input branches return a fixed triple and terminate. Thus both
source subprocedures meet the inherited total finite-call contract.

The live controller maintains `candidate=2**n`,
`candidate <= i < 2*candidate`, and `n` equal to the coded input length.
The exponent clock `(n+1)**j` is finite for every call and is not capped.
Candidate indices, encoded descriptions, clock exponents, input sizes and
arithmetic register contents remain unbounded. The number of *register names*
is fixed; it is not a value or tape-space bound.

For a fixed wrong candidate, the inherited characterization supplies a finite
input on which its acceptance bit disagrees with the required complement.
Every earlier input comparison terminates, so this input is eventually reached;
the candidate is rejected and the next candidate begins with one source beep.
A least correct candidate, when one exists, is reached after finitely many
rejections and then advances through all finite input indices silently. If
none exists, arbitrarily many candidates are rejected. This is the inherited
finite-source-event iff NP = coNP theorem. It covers incompleteness and
unsoundness of candidate acceptance and does not infer validity from finite
successes.

## Conservative tuple-return positivity adaptation

The old positivity checker handles tuple literal assignments but rejects tuple
procedure returns. The selected source has `e, initial, clock = instance(i)`.
The adapter makes a copy of each function solely for the static lower-bound
analysis. A tuple-call assignment becomes the original call expression,
followed by assignments of the constant zero to each named output. This copied
AST is never executed and is never passed as the source to code generation.

Retaining the original call expression is necessary: all argument reads and
all argument `%` and `//` sites must still be examined *before* output writes.
An early prototype deleted that expression; the selected source happened to
have the simple argument `i`, but the prototype was not a sound generic
extension. Independent review identified the issue. The final adapter keeps
the expression and tests reject, for example, `a,b = f(1//0)` and a parameter
whose positivity is unproved.

Every actual return component is a natural, hence has lower bound zero.
Replacing the component's lower-bound information by zero is conservative.
The unchanged checker computes only positive invariants justified by all
assignments and their preserving updates; zero assignments therefore cannot
supply an unjustified positive invariant. The retained RHS also preserves the
conservative read-before-assignment exclusions. The result is a valid
sufficient condition for the same positive-division specialization.

For this source, variable divisors are `radix >= 12` and `scale >= 1`; the rest
are positive integer literals. The emitted positivity certificate records each
checked site. The adapter does not assume that a tuple call returns a positive
value, does not remove any source call, and introduces no runtime machinery.

## Restoring unused register entries before the selector guard

The digit compiler reserves `$digit.index` even when the source contains no
matching digit intrinsic. Graph garbage collection removes its two unreachable
entry states. The exact shared-selector guard expects all allocated entry
rows, so it correctly rejected this input before the adaptation.

The new adaptation restores only absent whole states from the original
register-entry/index templates. It refuses a partially missing state, any
missing state with an incoming edge from the original graph, and any present
row differing from its expected template. It never overwrites a present row.
Consequently every trajectory beginning at any original state has exactly the
same next transition forever: it cannot reach an added state. This is a
finite graph argument, without bounded execution or a guessed invariant.

For the actual selected input, exactly four rows are added: INC and DECNZ entry
rows for the unused `$digit.index` register. Their original-state incoming-edge
count is zero. The original, unmodified shared-selector validator then checks
the complete inherited framework, register entries, index chains, dispatcher
inventory and bootstrap start. After selector replacement and graph collection,
unneeded restored entries disappear again. Register numbering is unchanged.
The final state count charges the actual linked table, not the temporary
restoration's rows.

## Arithmetic and control refinement

The inherited dictionary and liveness rules preserve source-defined live
values and nested call evaluation order, including delayed-reference aliases.
The reserved arithmetic cells are zero at complete expression boundaries.
The consuming quotient/remainder rule evaluates a pure divisor before consuming
an overwritten dividend, snapshots a self-divisor, and writes both results
only after computing them. Compact equality consumes its inputs and returns
exactly their equality bit. Positive division maintains remainder less than
the positive divisor and consumes a finite dividend. Constant arithmetic and
halving use the same existing unbounded kernels.

The selected option combination enables the inherited small additions,
subtractions, multiplications and halves. It leaves small comparisons and
small powers disabled. These options produce the measured smaller complete
machine; source length is not used as the cost metric. No new arithmetic
lowering rule is introduced by this transfer.

Closed-sequence factoring checks lexical closure before changing binary
parenthesization and preserves the exact ordered expansion of sequential
constituents. The zero-entry grammar pass supplies a post-fixed invariant on
zero/one/at-least-two register classes and checks its closure at every reachable
unfolded invocation. It replaces a shared zero-test row only if every admitted
invocation sees zero. Its finite structural rewrites preserve lexical transfers,
retained register operations and events. Each erased fragment is a finite
silent computation; a surviving divergent closed constituent is not discarded.
Thus it preserves the distinction between a finite and infinite event stream,
including an infinite silent tail. The independent certificate replay verifies
the invariant and each rewrite without trusting the producer's search.

## Shared selector, counted blank start and cofinal progress

The physical source bank uses the inherited unary blocks on one binary tape.
Each ordinary primitive has a finite binary control path `p`, a zero gap and
bank anchor `P`. The shared selector requires `P >= |p|+3`. It stores the
INC/DECNZ mode in the prepared control cell, traverses the finite index chain,
marks the selected nonempty block, returns to the mode bit, and joins the old
increment or decrement kernel on exactly the old tape/head configuration.
Every scan has a specified finite delimiter, even when register values grow.
The operation therefore completes after finitely many physical steps.

The five-state initializer uses the separate old-ABI register-zero entries and
its old preparation step. It is not silently treated as an ordinary source
call. The actual selected source has 42 allocated physical registers and
maximum leaf-path length 172, within the paid initializer's 1,909 zero-register
capacity and bound 3,822. The extra unused register is counted. These are
finite program dimensions; register values and used tape length remain unbounded.

The exact raw table's blank execution must reach source entry with head -3818,
no earlier events, and one-cells exactly `{-3821,-3820}` union `{3,5,...,3821}`.
After translating the control origin, this is the required clean zero bank at
anchor 3824. The separately retained literal certificate establishes this
finite premise for the actual raw bytes; an earlier machine's timing is not
substituted. The grammar invariant starts at this zero store. The counted silent
sink totalizes impossible preparation/selector rows, but cofinal progress comes
from valid simulation and finite scan termination, not from totalization alone.

Each finite source stage has finitely many arithmetic operations, each expands
to finitely many terminating primitives, and each primitive has a finite
physical realization. Induction therefore reaches every successive source
stage in finite physical time. The same argument applies after the last beep:
all finite input comparisons are still reached. Administrative transitions do
not emit repeated events.

## Exact quotient and the final marked event

The 821-state raw selected table is mapped to 819 states by an exact quotient
that verifies both rows of every raw state, preserves writes and L/R moves,
and preserves the designated B color. It is valid on arbitrary configurations
related by this state map. It does not need the optional contextual physical
quotient's ignored-row argument.

The 819-state machine starts outside B and is total. Every transition entering
B at time t is followed by a B exit at time t+1, and every B exit has exactly
one preceding entry. Moving the mark to B ingress changes no tape action and
shifts the ordered event times by exactly one physical transition. The next
quotient checks every marked row, including its event flag. This yields the
complete 818-state table, whose only marked row is `144 1 0 L 1 1`.

Neither physical halting nor the existence of another finitely visited state
is used. The completed binary machine runs forever, and it has finitely many
applications of that one marked transition if and only if the unchanged source
has finitely many beeps, hence if and only if NP = coNP.
