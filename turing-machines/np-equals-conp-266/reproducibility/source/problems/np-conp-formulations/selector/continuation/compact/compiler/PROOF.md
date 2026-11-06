# Direct argument installation and final-call return forwarding

This is the canonical proof for `direct_calls.py` and `return_forward.py`.
It changes the compilation of procedure boundaries, not the mathematical
search or the interpretation of any candidate. It assumes the inherited
natural-language compiler contracts and the source-liveness allocation proof
in `../../compiler/live_registers.py` and the preceding selected composition
in `../../arithmetic/COMPOSITION.md`. All registers contain unbounded natural
numbers. This is a conventional proof, not proof-assistant certification.

## Storage and arithmetic boundary invariant

At a complete expression or statement boundary, the five shared arithmetic
registers and copy scratch are zero. Each caller-owned temporary marked in
its `used` set has a separate physical cell; all other caller temporaries
are zero. Source cells and return slots are distinct from compiler scratch
and temporaries. The inherited allocator may identify two source cells only
under its interference certificate. Simultaneously read source variables
are mutually interfering. Arguments of one call are such a simultaneous
read group in the original source CFG.

Procedure calls form an acyclic graph. A caller has strictly greater call
height than each callee. Source cells in different active call heights and
the corresponding owned temporary banks are disjoint. The inherited
parameter clique also makes distinct parameters of one callee distinct.
`direct_calls.py` checks the relevant height, parameter, caller-read and
compiler-storage disjointness before emitting a selected lowering.

Every `clear`, `move` and `copy` terminates on finite natural inputs. A copy
preserves its source and restores copy scratch to zero. A move consumes its
source into an initially zero destination. All inherited arithmetic
expressions here are total on natural inputs, including saturating
subtraction, quotient zero on divisor zero, and remainder equal to the
dividend on divisor zero. Their loops terminate on each finite input.

## Direct argument installation

The selected call rule admits only a normal positional nonrecursive call,
with consuming-return mode enabled, at least one named or natural-literal
argument, no nested call anywhere in the argument group, and no destructive
source-read marker anywhere in that group. Unsupported or effectful cases
use the inherited lowering unchanged. Malformed argument counts remain
errors rather than acquiring a new meaning.

The inherited rule evaluates every argument left to right into an owned
temporary. It then clears each callee parameter and moves that temporary
into it. The new rule retains the relative evaluation order of all complex
arguments and captures each in its own owned temporary. It defers only
named reads and literal evaluation. With no nested call and no destructive
source reads, evaluation of a complex argument writes only compiler-owned
storage. Consequently all caller source cells retain their original values
throughout argument evaluation. Reading a named argument later returns the
same natural value; a literal has the same value and no effects whenever
it is evaluated. All admitted argument expressions terminate.

After these captures, the rule clears each callee parameter. A named value
is copied directly from its disjoint caller source cell, a natural literal
is constructed directly in the parameter, and a complex value is moved
from its captured temporary. Installation order cannot change another
argument's value: callee parameter cells are distinct from all caller read
cells, all captures, and each other. The construction of a large literal
uses the existing finite binary-doubling expansion with zero arithmetic
scratch; that loader and all of its operations remain in the counted table.

Thus at callee entry, every parameter equals its inherited value, all
owned argument captures have been consumed and freed, and compiler scratch
is zero. The same callee body and entry resets run. The ordinary path then
moves every return slot into a fresh caller-owned output, exactly as the
inherited consuming-return rule. The resulting caller state agrees on all
live source cells and owned values. The only omitted values are now-zero
intermediate argument cells, which are no longer allocated.

No new event occurs in argument installation. Call-free expression
evaluation is event-free, and the callee body retains its ordered events.
Reordering only the omitted pure reads therefore preserves the complete
ordered event sequence, not just its finite/infinite distinction.

## Final scalar call in an equality guard

The return-forward rule selects a guard `left == call(...)` or
`left != call(...)` only when the right call meets the direct-argument
contract above and returns exactly one value. Other guards use the
inherited lowering. This is a guard-level transformation, not a change to
generic scalar expression or assignment semantics.

First evaluate the left operand under the inherited operand contract.
It is either an owned temporary, a pure constant, or a caller source
reference. Then evaluate the right call fully, including the unchanged
callee body, but retain its result in its physical return slot rather than
moving it immediately into another caller temporary. The final-call rule
admits no subsequent call before this value is consumed. Any caller source
reference from the left is safe across the call because the callee has a
different, lower call-height frame. An owned left result is also disjoint
from every callee cell. The compiler checks the actual relevant aliases.

Load the left value into arithmetic register A by the inherited operand
rule, move the retained callee return into arithmetic register B, and invoke
the same equality kernel. Loading A can use copy scratch or the constant
loader, but cannot alter the disjoint callee return slot. The arithmetic
kernel therefore starts with exactly the two natural values it would have
received after the old return staging. It consumes A and B and produces
the same Boolean Q; inequality uses the same inherited inversion to A.
The return slot is zero after its move, just as after the inherited
consuming-return capture. The unneeded caller output temporary is never
allocated. All other owned values are freed at the same logical boundary.

The right call remains after the left evaluation, and its internal events
remain in order. Moving a natural between storage cells introduces no
events and terminates. The guard's branch decision is unchanged. Applying
this rule inside an `if` or `while` therefore preserves both branches and
every loop restart.

## Composition, progress, and limits

Induct on the finite acyclic call height and the source execution. At each
selected call boundary the two executions have equal live values. Every
replaced finite administrative segment terminates; callee termination or
progress follows the same source theorem and induction. At each guard
boundary the same Boolean is obtained. Unchanged source control therefore
visits the same candidate indices, tests, and source beeps in the same
order. No unbounded candidate, clock, branch or record parameter is capped.

The physical compiler still emits the complete unary primitive grammar,
binary register engine, selector, blank bootstrap and event adaptation.
There is no supplied input or external runtime. Its inherited primitive
simulation and finite-bootstrap proofs compose with the equal-value
boundary relation just proved. Every finite source stage has finitely many
primitive operations and physical steps. Cofinal source progress is thus
preserved, including infinitely many successful finite stages when no
candidate is correct. Exact primitive timings and physical beep times may
change; the complete ordered source beep sequence does not.

The separate source theorem then yields finite marked events iff NP=coNP.
The unchanged physical conversion marks ingress into B and shifts each
B-exit event by one physical step before taking its exact all-row event
quotient. Initialization still starts outside B. This preserves finiteness
and infinitude; no arbitrary state-visit convention is substituted.

`check_calls.py` supplies finite source/grammar differential checks,
including repeated names, delayed reads, large literals, nested-call
fallback, call effects, multiple returns, repeated invocations and guard
boundaries. Complete binary tables are emitted and counted for each fixture.
These finite checks support the local implementation contracts; they do
not prove unbounded arithmetic or decide the eventual silence of the full
NP=coNP search. Independent review and full physical runs are separate.
