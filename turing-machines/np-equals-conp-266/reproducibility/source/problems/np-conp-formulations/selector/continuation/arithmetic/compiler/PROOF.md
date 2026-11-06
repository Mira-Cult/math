# Direct affine arithmetic: author preservation proof

This proves the new rules in `lowerings.py`, conditional on the frozen natural
compiler, liveness allocation, grammar and physical-runtime contracts.  It is
an author proof, not an independent review or a proof-assistant artifact.  No
new NP/coNP formulation or permanent claim ID is introduced.  A new input
source still needs its own mathematical source theorem.

## Input and representation contract

The input is an accepted source in the frozen natural-number language.  Values
are unbounded naturals; subtraction saturates at zero; Boolean expressions
produce bits.  The selected inherited positivity analysis runs on the original
AST before lowering and discharges every divisor obligation.  All arithmetic
here emits the existing unary INC/DECNZ and structured control grammar.  There
is no external arithmetic oracle, fixed word size, supplied tape or new uncounted
primitive.

The pass inherits `HalfPairBuilder`.  Its four independent switches are
`affine_expressions`, `affine_updates`, `affine_assignments`, and `affine_forward`.
Disabled rules use the unchanged inherited lowering.  The implementation never
modifies the source AST.  Consequently the original whole-expression read sets,
last-read exclusions, source CFG and source register-interference obligations
remain available to subsequent allocation.

The five shared arithmetic registers A, B, Q, R and C, and the copy scratch S,
are zero at complete expression/statement boundaries.  Owned compiler
temporaries are zero when allocated and separate from source slots and shared
scratch.  A source slot may alias another dead source name, but simultaneous
reads and definitions are protected by the independently reviewed allocator.
Every physically simultaneous caller frame has a different call height.

## Pure weighted sums

`pure_scalar` admits only existing scalar literals/names, natural binary
arithmetic, `not`, Boolean expressions and single comparisons.  It excludes
every procedure call and unsupported expression form.  Thus flattening never
moves or omits an event, call, exception, mutation or potentially nonterminating
source procedure.  Negative literal syntax and subscripting are not accidentally
admitted through multiplication by zero.

`linear_terms` flattens addition and distributes multiplication by an integer
constant only while the accumulated coefficient stays in 0..8.  It retains the
left-to-right order of atomic terms.  All remaining operators, including
saturating subtraction, remain atomic.  Thus a value is represented exactly as
the natural sum of its weighted atom values.  In particular `4*(x-5)` denotes
four times the saturated subtraction; it is never replaced by `4*x-20`.
Larger coefficients use an ordinary inherited expression as an atom.  Zero
coefficients may omit a pure atom because every admitted arithmetic expression
terminates and has no source effect.  Omitting a last read may leave a different
finite value in a dead slot; dead values are already outside the allocator's
observation relation.

## The paid append operation

For distinct out, source and S, with S=0 and coefficient k in 0..8,
`append_scaled(out, source, k, consume)` has the following contract:

    out' = out + k*source_old,
    source' = 0 if consume else source_old,
    S' = 0.

All other registers are unchanged.  For k=1 it calls the existing move or copy.
For consumption, each successful source decrement appends k units to out.
For preservation it additionally appends one unit to S, then moves S back to
source.  Both loops terminate on the initial finite source value.  The result
holds for arbitrary finite initial out, including a partially built sum.

All relevant physical registers are distinct.  An expression accumulator is
an owned compiler temporary, disjoint from every source and arithmetic slot.
For an augmented assignment the destination is itself a source read, so it
interferes with every distinct RHS input.  For a direct assignment the
accumulator is shared register A, disjoint from source and owned slots.  The
allocator never pools the copy scratch with any of these registers.

## Expression accumulation

Allocate one zero owned output and append the weighted atoms.  Small constants
increment it directly.  A named source input uses the inherited last-read
marker to choose consumption or preservation.  A complex atom is evaluated
through `self.expression` into another owned temporary, then consumed into the
sum and freed.  The accumulating output remains allocated while that recursive
evaluation occurs, so temporary reuse cannot overwrite it.

Every duplicate source read in the original simultaneous expression group is
excluded from last-read consumption by the inherited compiler.  This protects
earlier delayed references as well as later reads.  Source names needed after
the expression are likewise preserved.  Source inputs used together have
different allocated slots even if some die after the expression.  Induction
over the term list gives the exact complete value, with the shared arithmetic
bank and S again zero.  The output is the sole new owned nonzero temporary.

## Direct augmented and ordinary assignments

For `x += rhs`, the rule requires that x occur nowhere in rhs and that rhs be
pure.  The append contract can then use x itself as the initially nonzero
output.  Every input read is evaluated with the old source values, and no
operation on a distinct source name can alias x because x is a simultaneous
read.  The result is exactly old-x plus rhs.

For an ordinary named assignment, complex atoms are captured into distinct
owned temporaries first, while the shared bank is zero.  They may be evaluated
before simple named terms because the complete expression is pure.  If a name
is read both in a captured atom and in a later simple term, the whole-expression
duplicate-read exclusion prevents consumption in either occurrence.  If a
captured atom consumes a unique last read, there is no later demand for that
old value.  Different simultaneously read names cannot alias physically.

After capture, A is zero.  Simple constants, named inputs and captured values
are appended into A; no complex evaluation starts while A holds the running
sum.  A unique plain occurrence of the overwritten target may be consumed
because its old value has no other occurrence in the expression.  In that
case its slot is already zero.  Otherwise the target is cleared only after
every RHS value has been captured or accumulated.  Moving A into the target
then installs the exact answer and resets A to zero.

Deferring this clear is essential: a fresh destination may physically reuse a
dying input's slot even when their source names differ.  Such aliasing is safe
because all reads finish before the clear.  A live input cannot alias a
definition by the inherited interference obligation.  When the old target is
itself read, it interferes with every other simultaneous input; early
consumption of its unique plain occurrence therefore cannot damage another
term.  Captured temporaries are consumed and freed exactly once.

## Forwarding an inherited complete result

For a complex scalar arithmetic/comparison atom, the pass can remove its final
`move(owned_output, shared_result)` when the generated sequence is exactly that
memoized move.  The inherited scalar lowering places the entire result in one
shared register, leaves its owned output zero until this last move, and leaves
the other shared registers zero.  The pass consumes that shared result directly
into the enclosing weighted sum, then releases the unused zero owned output.

The guard explicitly excludes a recursively affine expression.  Such an
expression builds its output incrementally, so its last move could be only the
last summand and would not justify whole-result forwarding.  The guard also
restricts forwarding to inherited binary arithmetic or single-comparison
expressions and checks the exact emitted last move.  No syntactic guess about
which register an operator should use replaces this structural check.

The append contract consumes the complete shared result and restores its zero
boundary, yielding the same enclosing sum.  The discarded owned output remains
zero and is not referenced by any emitted subsequent instruction.  The rule
therefore preserves both the value and all scratch/ownership invariants.

## Control, events and progress

These rules change only pure arithmetic or assignments.  They introduce no
source event, branch, candidate bound, clock bound or program-size bound.
Procedure calls and eventful expressions retain the inherited lowering.
The source-level live-value relation, outputs and ordered source events are
preserved at every statement boundary.  Temporary/dead-register snapshots and
physical event times are not claimed to be identical.

Every appended natural and captured expression is finite.  The append loops
strictly consume a finite counter and restoration is a finite move.  Every
recursive expression follows a proper AST subtree or an inherited finite
arithmetic operation.  Each source step therefore completes after finitely
many primitive steps.  Induction over arbitrary finite source prefixes gives
cofinal progress, so source eventual silence is preserved in both directions.

The unchanged grammar factorization, certified zero-entry simplification,
shared-selector simulation, totalization, full-row quotient and event adapter
then give the physical composition.  Actual register and leaf-path bounds are
checked on every complete build.  All raw and final tables, initialization,
scratch, addressing, control and event machinery are counted.  Exact
blank-entry and literal physical replay remain separate review receipts for a
frozen integrated candidate.  A source theorem for NP=coNP plus these compiler
and runtime obligations yields the same finite-event equivalence; bounded
execution does not decide NP versus coNP.

## Author verification

`test_arithmetic.py` recompiles the 52 inherited lifetime/half-pair fixtures
through this constructor and adds 19 affine/effect/prefix fixtures.  The latter
include repeated and delayed reads, a destination reusing dying input storage,
old-target reuse, complex capture, zero coefficients, saturated subtraction,
power/Boolean/comparison atoms, large constants, and an eventful call multiplied
by zero that must still execute.  Shared arithmetic and copy scratch are
checked zero at observed events.  Nonpure and unsupported ASTs are rejected by
the new rule and left to the inherited compiler.

These are source/grammar differential checks with complete finite-table
generation.  They are author tests, not independent review, proof-assistant
certification, literal execution of the selected full table, or remote CI.
