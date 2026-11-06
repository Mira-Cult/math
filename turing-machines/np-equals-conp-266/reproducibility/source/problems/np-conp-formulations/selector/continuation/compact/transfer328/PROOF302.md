# Normalized source and physical refinement for the complete 302 machine

This is the canonical new argument for source
`coordinator/source-consume.py`, SHA-256
`75ec1f57e1be96626a2ab559c890ab420e820eb0983ff16cc967665a2d44db63`,
and the literal table identified in README.md (historical reference: `README.md`; outside this selected-only export). No permanent claim
ID is introduced. The conventional mathematical argument, finite certificates,
independent reviews, literal execution and a Lean port are distinct obligations.

## 1. The inherited theorem and its exact interface

The theorem control is the frozen normalized source at
`../phase_search/coordinator/pair_normalize.py`, SHA-256
`7d98b2beb3676f7d0e4f0d6785a5a78d4817f05f23ec38c82635a3ea4b31a039`.
Its [endpoint theorem](../phase_search/PROOF.md) uses the independent-write,
relative-direction deterministic acceptance relation with an existential
initial certificate from [the source proof](../source/PROOF.md). The previous
[360 refinement](../binary_phase/PROOF.md) supplies the native record skip,
read/turn HALF branches and normalized marker/payload parser.

For every natural i, parse low-first pairs `(marker,payload)` until the first
zero marker, treating absent bits as zero. Starting at e=1, update e to
`2*e+payload` at every successful pair. The result is n=N(i), e=D(i), in the
reversed-payload convention relative to the old reference language. The caller
preserves i, including its arbitrary ignored higher suffix. Every even i has
n=0, and a high marker one may have a virtual zero payload. The final failed
marker is consumed from the working scan. In particular

    2^n <= D(i) < 2^(n+1)

for every finite i, including n=0, D(i)=1.

The compared bits must be `A(D(i),0,n)` and `A(j,i,(n+1)^j)`. A's initial
state is 1 and initial facing is positive. Certificate bits occupy cells
-1,-2,... and input bits occupy 0,1,... . For positive state s and observed
bit z, the selected unary record ordinal is s+z-1. Its value a independently
encodes write `a mod 2`, relative turn `floor(a/2) mod 2`, and next state
`floor(a/4)`. State zero is absorbing. Missing and truncated records have a
virtual zero tail, including overlapping state windows. C=0 rejects after
its unique empty-certificate attempt.

The inherited coverage theorem is unchanged: a complementary verifier must
initialize every positive workspace cell it uses, work within time and witness
bounds in parsed length n independently of the ignored suffix, preserve the
negative certificate during input preparation, and accept an empty prefix in
one transition. Description and exponent are the same j. Complete-prefix
padding supplies sufficiently large equivalent descriptions, while internal
runtime and witness guards prevent the enlarged external clock from adding
spurious acceptance. Both j=0 and n=0 give clock one. Fixed candidates are in
NP in ordinary bit cost; no unary implementation running time is being used
as the complexity measure in that theorem.

## 2. Reference witness capacity from the existing description

Let A_B(e,x,C) enumerate the finite integers B-1 through zero as initial
negative certificates, while retaining the same C-transition simulation.
If B>=2^C, then A_B(e,x,C)=A(e,x,C). Indeed, every C-bit word occurs among
zero through 2^C-1. Conversely a run of at most C transitions starting at
cell zero cannot inspect a negative certificate cell beyond the first C
positions. Truncating any attempted integer to its low C bits therefore
preserves every read, state, write, facing and head position through the
clock boundary. Extra attempted high bits cannot add acceptance. This is a
statement about initial certificate bits; simulated writes remain destructive
and do not change the protected enumeration master.

For the reference, C=n and B=D(i), so the parser's sentinel inequality proves
the premise. The new source sets `branch=e`, rather than constructing 2^n.
It tries e-1,...,0, at most twice as many attempts as the original reference,
with the same returned bit. At n=0 there is exactly the zero-certificate
attempt with zero transitions; its state remains 1 and it rejects. The
candidate still builds exactly 2^C and enumerates all C-bit words, including
all-zero and all-one words. Its clock remains exactly C=(n+1)^j.

At each attempt the master branch is decremented once and copied to working
left. Working right is reset to zero for the reference and to the complete
integer i for the candidate. Working state and steps are reset to 1 and the
phase's clock. Description, input, length and clock masters are not simulation
scratch. Destructive writes modify only the working halves, never the master
certificate integer or the retained outer input.

## 3. Explicit phases, result polarity and ordinal consumption

Inlining the two finite acceptance computations removes their generic
parameter capture and return interfaces. The source starts expected at zero;
reference success sets it to one, while reference failure leaves it zero.
Candidate success toggles it once, and candidate failure preserves it.
Thus at the comparison boundary

    expected = A(D(i),0,n) XOR A(j,i,(n+1)^j).

Expected is always Boolean. Its true toggle branch can therefore use
`expected -= 1`, and its false branch installs one. The final zero test
refutes exactly both equal-bit cases (0,0) and (1,1); either unequal case
silently advances i. Each candidate starts with one beep, and refutation
advances j and resets i. No P=NP deterministic-choice specialization occurs
in either phase.

On acceptance, a break exits the enclosing certificate loop. Its residual
branch value is dead: the next phase resets branch, or the next comparison
does. Removing `branch=0` before that outer break is therefore valid. This
reason does not apply to the preserved carried-address experiment's inner
step-loop break, where clearing branch is necessary; that experiment retains
the clear. The selected source continues decrementing a finite steps value
after simulated state zero, with the transition body guarded off, so it keeps
the inherited absorbing-state interpretation. It does not use early HALT.

Inside a positive-state transition, commuting `state-=1` before the
independent read-bit increment changes neither the ordinal nor the working
input half: the result is still s-1+z. It exposes an exact consuming guard.
The inherited skip loop consumes exactly that many complete unary runs and
their terminators, without accumulating discarded values. The selected run
is accumulated into a freshly zero state value, then decoded. Zero and
all-one descriptions, virtual terminators, arbitrarily repeated lookup and
overlapping windows are all covered by the inherited skip proof. The write
bit remains independent of the observed bit and of the turn bit.

The source therefore computes the same ordered normalized comparisons and
events as 387 and 360. Its internal attempt order and primitive histories may
differ. Every individual parser, finite clock, finite witness enumeration,
reset, simulation and comparison terminates on every finite input. If NP
differs from coNP, every proposed complement has a finite counterexample,
so j advances forever and emits infinitely many events. If NP=coNP, there
is a correct complementary candidate; the first such candidate that is
reached continues infinitely many correct, finite comparisons silently.
The source execution is infinite in either case. Finite events therefore
mean NP=coNP; silence is not an unfinished comparison.

## 4. Closed lowering rules and ownership

The transferred arithmetic contract is independently stated in
[control/PROOF.md](control/PROOF.md). It uses base N+1, not the donor's N+2.
The P=NP language, branch semantics and input frame are not transferred.

For `F=(N+1)^K`, F,N,K,B,Q,C are distinct logical coordinates; B,Q,C are
zero, while F may be stale. Clear F and set it to one. At each successful
decrement of borrowed K, increment restoration counter B, consume old F,
and add a preserving copy of N plus one to Q per old F unit. Move Q back
to F. After t iterations,

    F=(N+1)^t, K=K_old-t, B=t, Q=C=0.

At the exit move B back to K. Both masters N,K are restored, output is exact,
and all work is zero. Finite outer and inner countdowns, finite copies and
finite restoration prove termination for all naturals, including N=0,K=0.
The borrowed j is not observed outside this closed, event-free region.

For the exact certificate seed `F=1; S=K; while S: S-=1; F*=2`, borrow K
and use S as the restoration counter. After t doublings the invariant is
F=2^t,K=K_old-t,S=t,Q=0. Restoring K from S gives the exact original source
result with S=Q=0. Arbitrary stale F,S are cleared at the emitted macro
entry; contextual elimination of a clear requires its own zero-entry proof.
The selected main contains one such seed, for its candidate phase. This
still constructs the natural 2^C. No nested clock, actual-word odometer or
avoidance of witness-capacity construction is claimed.

Ordinary source liveness would not by itself protect output F from a master
whose last read is inside either new region. Both matchers explicitly add
their simultaneous-operand interference edges before frame allocation.
The scratch coordinates are existing distinct arithmetic work cells. Fresh
contextual and class-sum certificates then inspect every emitted primitive
inside the borrowed intervals; no unproved atomic multioperand instruction
is hidden from ownership analysis.

`coordinator/consume_guard.py` matches exactly
`if X: X-=1; body else: other`. One existing DECNZ is an exact implementation
for every natural X: on zero it leaves zero and chooses other; on positive
X it leaves X-1 and chooses body after the leading decrement. The matcher
needs no Boolean hypothesis. Only the source transformation of expected's
toggle uses its separately proved Boolean invariant. This single-operand
lowering has no additional aliasing or early-output-clear premise.

The selected fresh storage chain has 24 source logical coordinates, 21
allocated registers, 17 projected logical registers and 14 physical classes.
At a physical primitive boundary each class equals the sum of its ghost
logical coordinates; every other member of the operated class is zero.
This is not unrestricted aliasing. The exact allocation, projection, finite
control and 75 class-sum obligations are included in the complete parent.

## 5. Physical boundary relation, completion and events

The source-to-grammar boundary relation records the active lexical path,
head position, all ghost values, projected bank and zero work cells. Its
physical realization is the inherited unary bank with a prepared control
path, paid selector, operation entries and finite reserve. Native HALF
consumes a natural into its quotient and branches on its old low bit.
Every INC, DECNZ, HALF, preserving copy, move and closed region terminates
in a positive finite number of binary transitions at its admitted boundary,
preserving all unrelated blocks. The underlying segment proofs are in
[native composition](../native/COMPOSITION.md) and
[the native HALF proof](../compiler/native/PROOF.md).

The new maximum lexical path is 57, below the paid bootstrap span 3822.
Fourteen active classes fit its 1909 initialized zero fields. Literal blank
entry is checked separately; primitive induction applies thereafter. No
tape alphabet, track, caller tag or supplied program is an uncounted
parameter. The full blank-start writer and entire caller are in the table.

The complete producer has 312 raw states and its ordinary all-row quotient
has 309 B states / 308 marked states. Fresh completion derives the admitted
domain from the new names and raw quotient. The named semantic exclusions
are the inherited preparation, separator, HALF temporary and selector-entry
facts, with all raw preimages checked against those facts. A totalization
request is not itself a semantic exclusion proof. The new domain has 13
excluded quotient rows with 15 raw preimage row occurrences, including the
two sink rows. The sink has no admitted predecessor.

Only these rows change in the completed 309-state parent. All 605 retained
rows remain byte-identical to their old row values. The admitted run hence
agrees step for step, including head and tape, with the complete parent.
This is not arbitrary-configuration equivalence to its old silent sink.
The fixed completion partition then checks all 618 completed-parent rows,
keeps B a singleton distinguished class, and yields 303 B states. Every
state has both binary rows and every target exists. Discovery and fixed
replay are separate commands; no optimization search runs during replay.

The companion starts outside B and neither B row targets B. Marking ingress
into B therefore records each B exit exactly one physical transition earlier.
The event quotient checks all 606 ingress rows and produces 302 states /604
rows, with sole marked row `104 1 0 L 1 1`. It is derived from the new event
map, not copied from a former numerical state identity.

Administrative paths contracted by the grammar proofs are finite and contain
no jump-only cycle. Eliminated zero resets may have an empty local refinement;
they are grouped with the next retained source action. Every infinite source
execution has infinitely many retained positive finite primitive segments.
No administrative loop, restoration, clock or cleanup can cause false eventual
silence. The exact event correspondence and source theorem therefore transfer
to this literal, deterministic, binary, single-tape, blank-start machine.

## 6. Evidence limits

Independent source checks compare the actual source AST with a separate
signed-tape oracle. Storage and quotient checks inspect all finite equations
and deliberately damaged inputs. Independent literal engines agree on full
configurations from blank and at actual comparison boundaries; prepared
fixtures have a different stated scope. Their finite evidence supports the
general segment and endpoint proofs and cannot decide eventual silence.

The original 387 event times, the separately reviewed 360 trace, the older
407 source and the losing serial backend remain separately pinned. The
shared existential theorem alone does not identify this literal table.
Nonauthor model review is not external human review or Lean certification;
skipped GitHub jobs are not passing CI.
