# Source lifetime allocation

This is a new compiler continuation of the frozen shared-selector producer.
It does not replace the mathematical NP/coNP source theorem.  An arbitrary
source accepted by `build_live.py` has only a compilation claim until its own
mathematical theorem is supplied.  No permanent repository claim ID is allocated
here.  These are conventional author proofs; independent review is separate.

## Contract and inherited boundary

The input is an accepted finite, nonrecursive natural-number source of the
inherited compiler.  Calls have fixed positional arity.  Source variables are
unbounded naturals, and the existing arithmetic, guard, call, and consuming-read
proofs remain dependencies.  Repeated names on the left of one tuple assignment
are rejected by this pass.  No fixed word width or bounded source execution is
assumed.

The pass runs after source lowering and before closed-sequence factoring,
zero-entry tree simplification, binary generation, and shared-selector
adaptation.  It replaces source register names in every primitive occurrence.
Compiler temporary registers, the five arithmetic registers, the copy scratch,
and the optional digit-index register are never identified with a source slot.
It changes none of the source AST, arithmetic code, control labels, or events.

The older frame-pooling proof permitted aliases only between procedures at the
same call height.  This pass adds aliases inside one procedure when lifetimes do
not conflict.  The same strictly decreasing call-height rule continues to
separate all simultaneously active procedures.  The exact inherited sources
remain pinned by `selector/provenance.json` and checked before every build.

## Control flow and liveness

`function_cfg` constructs a finite directed graph of source statement boundaries.
An assignment reads its entire right-hand side and defines all its targets.
An augmented assignment also reads its target.  A conditional has both branches.
A loop has a body edge and an exit edge; retaining an impossible exit edge for
`while True` is conservative.  `continue` goes to the nearest loop guard and
`break` to the nearest loop exit.  Returns go directly to the procedure exit.
Call arguments are recursively included among the caller's reads; callee names
are not values.  The procedure body has no access to a caller's source slots.

Every internal return slot is a definition at an explicit return.  The exit
node observes every return slot.  Thus the return expression is evaluated before
those slots become live.  A possible fallthrough instead propagates the return
slots' existing zero values backwards, protecting the zero initialization kept
by the inherited definite-assignment pass.  The optional `--protect-returns`
comparison conservatively makes each return slot conflict with every local.

For each node v, the finite set equations are

    out(v) = union of in(w) over successors w
    in(v) = reads(v) union (out(v) minus definitions(v)).

Iteration from empty sets is monotone, terminates because the graph and name set
are finite, and gives the least fixed point.  Any value read before its next
definition along any executable path belongs to the corresponding `in` set;
prove this by working backwards from that read along the finite prefix of the
path.  A phantom loop exit can only add membership.  No terminating-execution
assumption enters this analysis.

## Interference obligations

The undirected graph contains a clique on each node's `in` and `out` sets,
a clique on all simultaneous definitions, and an edge from each definition to
every member of `out`.  The latter obligation includes dead definitions:
clearing or overwriting a dead local must not destroy a different live value.
All parameters form a clique because the caller installs them sequentially.
Parameters, entry-live names, and every retained entry-reset target together
form another clique, so the callee's initial clears preserve required arguments
and initial zeros.  All return slots form a clique because the caller retrieves
the distinct outputs sequentially.

A proper coloring gives one physical slot per color and call height.  Names
outside the source-owner inventory retain their original physical identity.
Every direct call edge is separately checked to decrease call height.  The
certificate records the source graph, fixed-point sets, interference graph,
colors, retained resets, return slots, parameters, height map, complete logical
register map and physical register count.  The no-search checker verifies the
set equations and all stated clique/edge obligations, then each coloring edge.
The test checker additionally rederives the CFG from the compiled source AST.
These are executable finite checks, not proof-assistant certification.

## Preservation at statement boundaries

Relate a source execution to the allocated primitive execution by requiring
that every live name at the current boundary has the same natural value in
its assigned physical slot.  Compiler-owned temporaries and shared scratch
satisfy their unchanged inherited zero/ownership invariants.  Dead locals need
not preserve their historical values; they are not observations of this
allocation interface.

At entry, caller parameter installation and retained entry resets preserve
all entry-live values by their clique.  On the blank source entry all slots
are zero, including aliases, so the initial relation also holds.

For an assignment, all names read anywhere in the simultaneous expression
group lie in `in` and therefore occupy different slots whenever their values
must be distinct.  The inherited compiler evaluates these expressions into
separate temporaries, or uses a proved specialized lowering whose named inputs
are among that same read set.  Its last-read consumption cannot erase another
live alias, because that other name would be in `in`.  Its output writes cannot
erase another live value, because every definition conflicts with `out`.
Simultaneous output targets are distinct.  A target may reuse an input's slot
when that input dies at the assignment; the input has then been captured or
consumed before the output writes.  In-place augmented arithmetic reads its
target, so the same `in` condition protects it.  Literal tuple assignments and
literal returns have no input reads and satisfy the definition obligations.

For a guard, its input values are correct by `in`.  The inherited guard code
restores any source cell it temporarily decrements before entering either
successor; any destructive last read is permitted only after its final use.
The successor-live set is contained in the guard's outgoing set.  A guard and
the selected branch therefore retain the relation.  The explicit backedges
give this argument to arbitrarily many loop iterations.  Break and continue
make no data writes and have the recorded successor.

At a call, caller values needed after the call stay in its height's bank.
Arguments are evaluated before parameter installation; the parameters are
mutually distinct and callee storage lies at a smaller height.  Apply the
inductive procedure proof.  An explicit return evaluates all return expressions
before writing its mutually distinct result slots.  These may reuse dead local
or parameter slots: no local computation follows the return, and the caller
retrieves each result before another call can reuse that bank.  If execution
falls through, the return slots' entry zeros are live throughout that path,
so all intervening writes are forced into different slots.  In either case
the caller receives the same outputs.  Sharing storage with an inactive sibling
procedure has no observable effect, as in the inherited frame-pooling proof.

`beep()` changes no source data and remains in the same source control flow.
Thus the allocated program has exactly the ordered source event sequence.
The relation preserves only live source values and procedure results; it does
not claim identical dead-cell snapshots or primitive instruction counts.

## Progress and physical events

An alias may leave a different finite value in a dead slot.  Every subsequent
inherited clear still terminates on that finite natural, and cannot damage a
live alias by the definition/entry-reset edges.  All arithmetic inputs actually
read are correct finite naturals, all owned scratch contracts still hold, and
the unchanged primitive proofs give finite completion of each source step.
Induction on any finite source prefix therefore gives a finite primitive prefix
reaching its corresponding boundary.  This establishes cofinal progress, not
merely partial correctness if checkpoints happen to be reached.

The inherited grammar factoring and verified zero-entry tree pass preserve
that ordered primitive computation up to their proved finite administrative
steps.  The shared-selector physical simulation preserves every primitive,
and its unbounded register representation has the same termination proofs.
The paid five-state bootstrap is included, and every build checks its actual
register count is at most 1909 and maximal grammar leaf path is below 3822.
An exact blank-entry literal replay is a separate required receipt for a frozen
selected table.  No preloaded program, interpreter input or external observer
executes any part of the machine.

All missing physical rows are explicitly totalized, and every state and both
binary rows are counted.  The ordinary physical quotient is checked on every
row.  `machine.tm` emits on B exits.  `events.tm` moves that mark to its incoming
row exactly one transition earlier and then applies an ordinary event-respecting
all-row quotient.  These existing adapters change neither finite versus infinite
event behavior nor the eventual-silence polarity.  They do not substitute
physical halting or existential finite state visitation.

Combining this compiler theorem with a separately proved complete source
theorem yields the same finite-event iff NP=coNP equivalence.  The finite tests
exercise local invariants and compilation, not either possible resolution of
NP versus coNP.

## Shared halving for a simultaneous pair

`half_pairs.py` is a separate, optional exact arithmetic specialization.  Its
syntactic guard accepts only two distinct named targets with right-hand sides
`x % 2, x // 2`, where the dividend `x` is the same named variable and the divisor
is the integer literal two.  There is no effectful expression to reevaluate.
It therefore preserves the inherited simultaneous evaluation convention.

At the statement entry all five shared arithmetic registers are zero.  Copy
the old dividend into A, or move it if x is one of the overwritten targets.
The inherited `half_kernel` removes units from A in pairs.  Each complete pair
increments Q; the possible final single unit leaves R=1.  Thus after finite
completion A=0, Q=floor(x/2), R=x mod 2, and B=C=0 remain unchanged.  The kernel
terminates because each iteration removes one or two units from the initial
finite A.  It is exactly the already-paid kernel used by scalar/in-place
halving, not a new uncounted arithmetic instruction.

Clear each destination unless it is the consumed input, which is already zero,
then move R to the remainder destination and Q to the quotient destination.
The destinations are distinct; if one is the input, the input's old value has
already been captured.  All five arithmetic registers are zero afterwards.
When x is not a target the initial copy preserves it.  The source-liveness
allocation proof applies because both targets are simultaneous definitions and
the input is a read; any required old input value conflicts with the outputs.

The resulting statement has the same source outputs and no events, and always
finishes in finite time.  Replacing the general divide-by-two call changes only
finite administrative work.  `half-pairs.json` records every exact syntactic
site and its consumed/preserved input convention.  The complete machine may
then omit the general division kernel if no remaining source operation needs
it; the counted reductions are obtained by actual whole-machine generation.
