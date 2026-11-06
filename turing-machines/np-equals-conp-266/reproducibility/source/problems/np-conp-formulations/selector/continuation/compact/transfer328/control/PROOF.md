# Closed destination clock for the normalized NP=coNP source

The author construction in `machines/borrow358` has358 marked states,359 B-exit
states and362 raw states, with eighteen physical register classes. The marked
table SHA-256 is `1ad822efa645c6086a305406e5d2ace3f5705c76e3e0ca65ca46eabab0a1616d`.
This is a complete construction before any new excluded-row completion. It is
not independently accepted merely by appearing here. The companion ordinary
named-clock source compiles to367/368/371 states and is preserved too.

## Source and donor scope

The source is `source-clock.py`. Relative to the frozen normalized parser source
in `../../binary_phase/control/parser/source.py`, it names
`clock=(n+1)**j` before the two calls and passes that value to the candidate.
Neither acceptance implementation nor either returned bit changes. Computing
the natural power is total and event-free. Hoisting it before the reference
call therefore leaves the ordered compared input pairs and designated events
unchanged. No exact old primitive trace or physical timestamp is asserted.

The donor is P=NP publication `9834b2b63f6709089a72766f4771eed8d92dc827`, specifically
`frontier/clocked/architecture_v2/direct_clock/borrow_region.py` and its `PROOF.md`.
Only the closed borrow/restore arithmetic contract is transferred. The NP
compiler emits its own binary table. The base is N+1, not the donor's N+2;
the normalized source still makes both certificate-existential calls with
the original clocks. No deterministic-choice specialization, canonical P
input frame, candidate-pair enumeration or P-language theorem is transferred.

The existing [normalized source and physical composition](../../binary_phase/PROOF.md)
remains the theorem control: finite designated events iff NP=coNP, infinite
physical execution in both cases, and infinite events iff NP differs from coNP.
All normalized-prefix suffix, initialization, empty-prefix, certificate and
complete-description-padding obligations are unchanged.

## Exact closed region

The matcher accepts exactly one assignment `F=(N+1)**K`, with the integer
literal one and three distinct named source variables. Six logical carriers
F,N,K,B,Q,C are distinct. F may contain stale data, N and K are arbitrary
naturals, and B,Q,C are zero. The carrier C is the existing preserving-copy
scratch; B and Q are existing arithmetic work cells. Every other logical cell
is preserved.

First clear F and set it to one. For each successful decrement of K, increment
B, consume the old F, and add a preserved copy of N plus one to Q per old F
unit. The inherited copy is additive:

    (N,Q,C) -> (N,Q+N,0).

After the inner countdown, F is zero. Moving Q into F therefore installs the
product F_old*(N+1) and empties Q. After t completed outer iterations:

    F=(N+1)^t, K=K_old-t, B=t, Q=C=0,

with N unchanged. At the outer exit K=0 and B=K_old. The paid terminating move
B into K restores the exponent and clears B. The sole normal exit thus has
F=(N_old+1)^K_old and restores N,K,B,Q,C to the required values. This applies to
K=0, which gives F=1 without multiplication, and N=0, which leaves F=1 at every
outer boundary. No fixed bound on either natural is assumed.

Termination follows from the finite stale F countdown, decreasing outer K,
decreasing inner old F, the finite preserving N copy and its scratch return,
and the final finite B restoration. Intermediate borrowing of K is permitted
only inside this closed region. There is no event, call or nonlocal source
escape. Every entry resets F and every exit follows exponent restoration.

## Source allocation and physical ownership

Ordinary source liveness could assign F the same carrier as N if N were dead
after the assignment. Such an alias would be unsound because this lowering
clears F before its final read of N. `clock_region.installed` therefore adds
the three simultaneous-operand interference edges before source frame
pooling. These edges are explicit in the allocation certificate. The ordinary
source CFG and liveness equations otherwise remain unchanged.

After this allocation, the ordinary contextual analysis, finite control plan,
register projection and zero-peer class-sum coalescence are regenerated.
At every emitted INC or DECNZ, all other logical ghosts sharing its physical
class are zero. The source allocation alone is not used as an intermediate
physical ownership proof. The borrowed K, restoring B and inner copy work
remain visible as ordinary operations to those checks. No new atomic move,
unproved multi-operand alias or physical arithmetic kernel is introduced.

For this complete table the actual clock graph occupies retained rows22
through36, with sole outside ingress13->22 and sole exit35->37 after restoration.
`check_clock.py` derives the region from its exact fifteen-row
recurrence, checks all edges and source-allocated and physical operands, and
executes the actual rows on finite arbitrary-stale-output fixtures. The exact
incoming and outgoing edges are recorded by the checker rather than inferred
from the numeric row range. These numbers describe this parent graph only.

## Composition, progress and evidence boundary

The binary realization uses the inherited finite positive natural operations,
native half, selector, return, whole-bank layout and zero-tape bootstrap.
Initialization, both call interfaces, normalized parsing, outer enumerations,
both comparison outcomes, event adapter, scratch cleanup and totalization are
all present and counted. Each state has both binary rows and every target is
present. The raw, B and marked quotients are checked on every row; numerical
state identities and excluded holes from earlier machines are not transferred.

Every finite comparison still terminates, since only a total exact power
implementation changed. Infinite correct comparisons give infinitely many
retained physical segments. Finite administrative rewrites are grouped with
the next retained operation, and the finite control checker rejects every
administrative-only cycle. Silence cannot result from a stalled clock.

`build.py` replays fixed plans only; `measure.py --discover` is the explicitly
separate deterministic construction-plan discovery command. The finite
fixtures support the universal recurrence and ownership arguments; they are
not blank-start evidence or an eventual-silence test. Nonauthor mathematical
review, binary review, remote CI and a Lean port are separate deliverables.

## Closed certificate seed, complete356 comparison

`seed_region.py` adds a separately selectable exact lowering of these three
source statements, in any function:

    F=1
    S=K
    while S:
        S-=1
        F*=2

The complete candidate `machines/seed356` combines this region with the same
borrowed exact clock and unchanged source. It has356 marked/357 B/360 raw
states, eighteen classes and207 arithmetic/control classes. Its marked hash is
`3253117e5eb0b85240f37923155e11d4d46ae8073b705edfe0b62b2b9a39678d`.
This is an actual complete measured candidate, not a sum of component costs.

The four logical operands F,S,K,Q are distinct; Q is existing arithmetic work
and is zero at entry. F and S may be stale and K is arbitrary. Reset F to one
and S to zero. For each successful decrement of K, increment S, consume F into
Q with two Q increments per unit, and move Q into the now-zero F. The invariant
after t complete doublings is F=2^t, K=K_old-t, S=t, Q=0. When K reaches zero,
move S into K. The exit has F=2^K_old, S=Q=0 and restored K, exactly the source
block's result. All other cells are preserved. Finite resets, decreasing K,
finite old-F doubling and finite restoration prove termination. K=0 produces
one branch and zero scratch. The unchanged acceptance loop decrements this
branch before trying the unique empty certificate and rejects when its clock
is zero, as required.

Explicit source interference protects F,S,K through the entire region. The
fresh primitive analysis and class-sum certificate include all borrowed-clock
and doubling operations; the existing source allocator is not asked to infer
their new lifetimes. Both actual calls contain this same closed region. In
this complete source S is already zero at each seed entry, and the contextual
proof removes its redundant reset. `check_seed.py` verifies that actual entry
mask before testing the two resulting eleven-row recurrences. Its prepared
fixtures therefore require S=0; the more general emitted-macro contract above
still includes the paid reset before contextual simplification.

No certificate word is ever exposed to destructive simulation as the master:
the unchanged subsequent branch countdown retains its independent natural
master and copies it to the simulated negative half-tape at each attempt.
The seed remains the actual natural2^C and does not claim a nested-clock or
word-odometer breakthrough. Its two-state gain is retained only as a measured
closed-region transfer into the whole machine.
