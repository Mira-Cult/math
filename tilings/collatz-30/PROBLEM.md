# Small polygon recurrent tilings for full Collatz

## Statement

Let C(n)=n/2 for even positive n and C(n)=3n+1 for odd positive n.
Full Collatz means forall n>=1 there exists t>=0 with C^t(n)=1.
This problem seeks a small finite set P of explicitly specified simple polygons
and a precisely charged geometric acceptance condition.

Track A asks for full Collatz iff there exists a completed legal plane tiling by P,
with no observer. Track B asks for full Collatz iff there exists a completed legal
plane tiling T by P satisfying the fixed geometric recurrence R(T).
These are different problems. Neither equivalence is inferred from finite diagrams.

## Goals

Construct and measure direct finite arithmetic row relations, their initialization,
successor/reset and growing-width scaffold, exact polygon geometry, and an observer
compiler. Prove both directions of the completed-plane equivalence before claiming
an upper bound for the target model. Record independently reviewed and finite
computational evidence separately. No minimality claim is intended.

## Model and scope

The primary geometric model allows translations and rotations, forbids reflections,
and consists of pairwise interior-disjoint copies whose union is R^2. Edge-to-edge
placement is NOT assumed. Coordinates, maximal straight side counts after exact
collinearity simplification, shape count, total/maximum sides, generator size,
coordinate bit lengths, and observer size are separate costs.

No tile is supplied externally and no coordinate origin or infinite boundary is
prescribed. A seed-shaped *intrinsic* corner is a prototile whose legal contacts
force a whole initialized computation if it occurs. Its occurrence and recurrence
on its own forward spine are explicit parts of Track B acceptance; they are not
assumed of every legal tiling. Rootless tilings are rejected by this grounding
condition. The exact resulting quantifiers and proofs are in
[the canonical selected polygon theorem](manuscripts/polygon-v3-theorem.md).
This is a static completed-tiling existence problem.

The selected native relation stores two positive fields (odd saved target n,
active value v), initially (1,1). Its nonreset steps are (n,v)->(n,2v) or
(n,3w+1)->(n,w) for positive odd w; each reverses one ordinary Collatz edge.
Equality v=n permits (n,n)->(n+2,1) with one event. A finite reverse path from1
to n certifies n's finite forward path to1. Infinite events cover all odd targets,
hence all positive inputs. Legal rooted runs are nondeterministic and may remain
silent. One event per certified odd target preserves infinitude, not the literal
17-state beep trace. Earlier forward all-input and shortcut constructions are historical controls,
not dependencies of this release.
The selected representation stores halves n=2h+1, v=2a+p in LSB-first binary,
with p synchronized by the spine. Rooted rows are right-infinite bit streams.
Under the explicit acceptance recurrence, every row has finite support and
represents a unique ordinary positive value, with a finite carry core followed
by its zero loop. Nonstandard legal active streams have no later RESET and
cannot pass R. This is a changed contract from the prior finite-frontier source,
whose historical theorem remains valid at its own revision. No end marker is
silently assumed or supplied by the observer.

Ordinary finite Wang plane tileability is Pi^0_1. Full Collatz has the displayed
Pi^0_2 syntactic form; this fixed statement has not thereby been proved complete
for that class. No generic effective Pi^0_2-to-Pi^0_1 reduction follows. This is
not an impossibility proof for the fixed Collatz statement, nor a classification
of arbitrary polygon sets specified by exact real coordinates.

