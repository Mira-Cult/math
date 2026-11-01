# Unseeded stream frames with thirty and thirty-one source types

## Scope and changed representation contract

This manuscript proves the source-frame and completed-plane obligations for
[`spine_frame_v3.py`](../code/spine_frame_v3.py), the 30-type half-value source,
and [`scaffold_v3.py`](../code/scaffold_v3.py), its separately retained 31-type
full-value control. Their arithmetic proofs are
[the half-value theorem](arithmetic-v3.md) and
[the unchanged 26-type stream theorem](stream-arithmetic-v3.md).
These are ordinary mathematical proofs with finite implementation checks;
independent review bindings are separate. A source-type count is not itself
a polygon upper bound. The geometric compiler and actual observer must also
be specified and reviewed.

Unlike the finite-width v2 frame, these sources use right-infinite bit rows.
Every rooted legal row has a precise compatible-residue interpretation, but
some legal silent rows do not represent ordinary integers. **Every arithmetic
row in the accepted ROOT's forced quadrant has finite support and represents
ordinary positive arithmetic.**
That conclusion is proved from recurrence and a finite future reset, rather
than from a local end marker. Infinite nonstandard rows are explicitly legal
nonaccepting exceptions. No finite prefix of such a row is silently promoted
to its entire encoded integer.

The removal of finite frontier types is the source of this compression. It
does not move an integer test into the observer: the observer continues to
recognize an intrinsic root and one fixed local event at unbounded logical
heights. The full equality/reset relation remains in the tile alphabet.

## Quantifiers before construction

For either source, a legal source tiling is a map from all of Z² to its finite
set of oriented Wang types, with matching adjacent edge colors. No tile,
initial row, boundary or origin is preplaced. Let delta and e be the entries
in the following table:

| Source | Number of types | Event column delta | Event east color e |
| --- | ---: | ---: | --- |
| Half-value parity spine | 30 | 0 | q6, the RESET spine's start carry |
| Full-value stream | 31 | 1 | q1, the first RESET digit's outgoing carry |

Define the source recurrence by

    R_source(tau) iff there exists o in Z² such that
       tau(o) is ROOT, and
       for every integer K>=1 there is an integer j>=K with
           east(tau(o+(delta,j))) = e.

The same actual ROOT precedes every time threshold. The coordinates here are
root-relative coordinates in the source array, not an externally supplied
geometric origin. A polygon version must compile ROOT, e and these offsets
into fixed geometric predicates in its intrinsic frame.

**Source theorem.** For each of the two literal source sets, full positive
Collatz holds if and only if a completed legal whole-plane source tiling
satisfying its R_source exists.

Every legal tiling has the structural interpretation stated below. Not every
legal tiling is rooted, not every rooted tiling is standard, and not every
standard rooted run resets infinitely often. The theorem uses existential
acceptance. Both source sets tile ordinarily without a Collatz assumption.

## Literal interfaces and full accounting

All four-tuples below are (N,E,S,W). Write d_ab for a bit-pair data color,
B for horizontal background, q_i for carry colors, and S or S_p for spine
colors. Data colors and spine colors are disjoint. B is disjoint from every
carry. The 31-type source also uses one distinct initializer color I.
There is no extra vertical background color: background vertical edges are d_00.

### Thirty-type half-value source

The 24 arithmetic types encode n=2k+1 and v=2a+p. The bit pairs in a row
encode k,a, while the actual spine's south/north colors encode the input/output
parities p,p'. The four charged spine types are:

| Type | Tuple |
| --- | --- |
| DOUBLE0 | (S_0,q0,S_0,B) |
| DOUBLE1 | (S_0,q1,S_1,B) |
| PREIMAGE | (S_1,q4,S_0,B) |
| RESET | (S_1,q6,S_1,B) |
| BG | (d_00,B,d_00,B) |
| ROOT | (S_1,B,d_00,B) |

Thus there are 24+4+1+1=30 types, eight horizontal colors and six vertical
colors. ROOT is index 29 and RESET spine is index 27 in the deterministic
literal enumeration. ROOT is the only type with the adjacent color pair
N=S_1 and E=B. Neither of those colors alone is a globally unique root marker.

East q6 occurs on digit 6 as well as RESET spine 27. At a site in the actual
root's spine column, however, only a spine type can occur; among those types
q6 identifies RESET exactly. Its right-infinite row supplies the complete
comparison a=k, successor k+1, and reset active value v'=1.

### Thirty-one-type full-value source

The retained source uses the unchanged 26 arithmetic types, storing n,v
directly. Its five frame types are:

| Type | Tuple |
| --- | --- |
| CHOICE spine | (S,q0,S,B) |
| DOUBLE spine | (S,q7,S,B) |
| BG | (d_00,B,d_00,B) |
| ROOT | (S,I,d_00,B) |
| INITIAL | (d_11,B,d_00,I) |

Its total is 26+2+1+1+1=31, with ten horizontal colors and five vertical
colors. ROOT is index 29 and INITIAL is index 30. East q1 occurs on digits 0
and 19; only 19 has an allowed initial carry on its west, so the event meaning
is restricted to the first digit column. This preserves the contextual
distinction of the reviewed v2 alphabet.

## Initialization forced by the upper infinite row

The following classifications hold literally in both sources:

* Only digits have a carry on their west, and every digit has a carry on its east.
* Only spine types have a spine color on their south. Only ROOT and spine types
  have spine colors on their north.
* A tile with west B is BG, ROOT or a spine. Among those, only BG has north
  equal to a data color; that color is d_00.

The 31-type source additionally has only INITIAL with west I and only ROOT
with east I. All these statements are checked from the emitted tuples by
`frame_checks`; the associated proof is just inspection of the displayed
frame types and the disjoint arithmetic namespaces. In particular, **it is
false that only BG has north d_00**. The argument does not use that former
finite-frame property.

Normalize one actual ROOT occurrence to (0,0). Its north spine color forces
a spine at (0,1), and thereafter a spine at every (0,y), y>=1. In the
half-value source its successive colors also force the parity supplied to
the next row. A spine's east edge is a carry. Since every west-carry type
is a digit and every digit emits another carry, induction in x forces
digits at every (x,y) with x>=1 and y>=1. This argument precedes any claim
about the initial row's data or the exterior.

For the 30-type source, ROOT's east is B. The tile at (1,0) therefore has
west B, and the digit immediately above it requires a data color on its
north. The third classification forces BG. Its east is B, so the same
argument inductively forces BG at every (x,0), x>=1. Their north data is
the all-zero pair stream. Together with ROOT's north S_1, this gives exactly
k=0, a=0, p=1, hence n=v=1.

For the 31-type source, ROOT first forces INITIAL at (1,0), with north d_11.
INITIAL's east B starts the same argument at x=2. The entire remaining
initial row is BG, yielding exactly the stream d_11,d_00,d_00,... and hence
n=v=1.

No externally supplied infinite boundary has been used. The forced infinite
zero row is a consequence of the finite local alphabet in an already completed
whole-plane tiling. Nor is this an assembly procedure or a hypothesis that
the intended outside region was filled before the computation.

## Root uniqueness, exceptions and coverage

There is at most one ROOT in any completed legal source tiling. Two in one
column contradict the upward spine forced by the lower ROOT: ROOT's south
is data, while each upward site must have a spine color on its south. If
two roots occupy different columns, choose a row above both roots. The left
root forces a digit at the right root's spine site, which is impossible
because the source types are disjoint. This is stronger than the widening
finite-cone argument: the entire right-hand row is already forced.

The root's orientation and row direction are part of the oriented source
model and must be provided intrinsically by a geometric compiler. In a
faithful compiled polygon tiling, a common rotation or translation changes
only the normalization used in this proof. Arbitrary independent rotations,
fault lines and shifted boundary phases remain obligations of that compiler,
not assumptions added to this source theorem.

Rootless source tilings, including all-BG and limits in which the root has
escaped to infinity, fail R_source. The proof does not assert that every
legal tiling has a root. Other exterior components below or outside a root's
forced quadrant need not have the canonical background description; they
cannot change its initialized rows or supply its events. Unframed infinite
backward histories cannot replace the actual ROOT tested by acceptance.

## From legal streams to finite positive accepted rows

The two linked arithmetic theorems apply to every right-infinite rooted
row without pretending that a finite terminal carry was checked. They read
the carry equations as identities of all finite binary residues. Starting
from the initialization just proved, the saved target is always a standard
positive odd integer: it is copied by nonreset operations and advanced by
exactly 2 by RESET. Equivalently, the half-target k starts 0 and increases by 1.

An actual RESET requires equality at every digit, not merely the first bit.
In the 31-type source it enforces v=n; in the 30-type source its input parity
is 1 and it enforces a=k, again giving v=n. Its complete output active stream
is 1. Since n is a standard finite integer, this reset is a completed finite
arithmetic operation followed by a forced zero tail. A first local event
motif whose comparison would fail at a later bit has no extension to the
claimed completed tiling.

Now take any earlier row before a later RESET. The active value at that
RESET is a known positive standard target. Moving backward through each
of the finitely many intervening rows forces a positive standard predecessor:
a reversed DOUBLE divides a positive even value by 2; a reversed PREIMAGE
maps a positive odd value w to 3w+1. The linked carry proofs establish these
identities from all binary residues and exclude a hidden infinite carry.
Thus every earlier row in that finite segment is standard. If a reset lies
inside the segment, its output is 1 and the same argument begins again on
the preceding segment.

Under unbounded RESET recurrence, every logical row lies before some RESET.
Consequently every accepted row has positive standard active value, a standard
saved target, and finite digit support. Each such arithmetic row ends
in its original finite-word zero-carry final state and then repeats the
corresponding all-zero self-loop forever. There is no ambiguity about its
integer value, no phantom carry or nonstandard preimage in an accepted run,
and no infinite-duration reset. The endpoint is semantically determined by
finite support and the carry theorem; no local end-marker claim is made.

Conversely, once any rooted active stream becomes nonstandard, it cannot
precede any later RESET. Such a run may continue legally forever, but its
event set is finite and it fails acceptance. This explicitly classifies the
new exceptions introduced by removing the frontier. Rooted standard runs
can also remain silent forever; standardness alone is not acceptance.

## Completed constructors and both Collatz implications

For an infinite valid row sequence from the initialized values, place the
actual ROOT on row 0, the forced INITIAL if required, and BG at the remaining
initial-row sites. Above it, place the appropriate spine and the complete
right-infinite digit row. Fill x<0 and y<0 with BG. All interfaces match:
spines have west B, ROOT has south d_00, initial data is the proved zero
stream (with d_11 in the full-value source), and adjacent arithmetic rows
share their entire output/input bit streams and, when present, parity.
This specifies every site of Z², not just a finite computation diagram.

The standard `WitnessTiling` constructors store a finite valid arithmetic
certificate for each requested row and return its exact zero-loop tile at
every greater column. Their `tile_at` methods therefore specify the entire
infinite row, rather than cutting it off at the stored finite prefix. The
quiet policy doubles forever at target 1 and is unconditionally total.
All-BG is another unconditional whole-plane tiling.

Assume full Collatz. For targets 1,3,5,..., take each finite ordinary trajectory
to its first 1, reverse it into a permitted inverse path, then RESET. Every
block is finite and positive. The arithmetic growth bound supplies finite
certificates of arbitrarily large required width; their zero tails complete
the rows. Concatenation yields unbounded genuine event times, and the completed
constructor therefore satisfies R_source. The accepted policy implements
this existence construction. It is total under Collatz and may be partial
if a target fails; it is neither the observer nor a total decision algorithm.

Conversely, an accepted completed tiling has the actual unique initialized
root described above. Every counted marker is a complete RESET in that same
rooted sequence. Between initialization or the last reset and the next reset,
the active value starts at 1, the target is constant, and every nonreset edge
is the reverse of a genuine positive Collatz edge. At the reset the active
value equals the target. Reversing that finite segment proves its forward
convergence. Resets advance targets by exactly 2, so infinitely many events
certify every positive odd target. Every positive integer reaches its odd
part by finitely many even steps, giving full positive Collatz.

If a least failing odd target b exists, no reverse path from 1 can complete
its reset, whether failure is cyclic or nonperiodic. Any legal rooted run
has at most (b-1)/2 events and may have fewer because it explores silently
on an earlier target. Neither an infinite nonstandard stream nor duplicated
spatial copies of a bounded prefix can evade this argument: R_source fixes
one root before its universal threshold, and that root is unique.

## Actual nonstandard completed examples and finite tests

Both source modules include `NonstandardWitnessTiling`, an exact completed
array whose full active values are

    1, 2, 1/3, 2/3, 4/3, 8/3, ...

interpreted as compatible binary residues, with saved target 1 throughout.
The first edge is DOUBLE and the next is PREIMAGE because 3*(1/3)+1=2.
The output predecessor is odd in the binary-residue sense. All later edges
are DOUBLE. The half-value source correspondingly uses active half-value
-1/3 when the full active value is 1/3 and parity is 1.

These rational streams have exact computable prefixes using odd-denominator
modular inverses or the equivalent bit recurrence. They satisfy the complete
local equations for every prefix, so the infinite formula gives an actual
legal source tiling, not an approximate numeric example. After entry into
this nonstandard part, a value 2^k/3 cannot equal target 1 because 2^k cannot
equal 3. No RESET occurs. The example demonstrates why ordinary rooted
tileability or a finite local event candidate cannot replace recurrence.

The two source test programs each have seven tests. They check the actual
color classifications, root/event contexts, both full-plane constructor
policies on finite windows, exact inverse certificates, arbitrarily distant
zero-tail queries, and the completed nonstandard example's interfaces. They
also reject a proposed reset whose low equality bits agree but a later bit
fails. The 31-type suite checks the complete closed-pair universes described
below. These finite checks support the emitted implementation; the infinite
classification and both implications are the mathematical arguments above.

## Closed-pair fusion for the thirty-one-type control

The 31-type source has two disjoint closed families of east-west pairs:

| Interface | Only left type | All possible right types |
| --- | --- | --- |
| I | ROOT 29 | INITIAL 30 |
| q0 | CHOICE spine 26 | first RESET digit 19, first PREIMAGE digit 22 |

These statements follow from the full literal tuple universe, not only a
canonical example. In particular q0 has no incoming arithmetic transition.
Thus every occurrence of each listed participant belongs to exactly one
such pair, even in a rootless or nonstandard source tiling. The two families
share no participant. Replacing the five participant types by the three
pair-union types leaves 29 types at the level of a proposed geometric fusion.

For any faithful polygon compiler, if the specified adjacent pair unions are
simple polygons and their expanded boundaries are measured, the converse is
particularly direct: subdivide every fused copy along its fixed internal
interface. This gives an actual tiling by the original polygons, under the
same translation/rotation/no-reflection model, so the original global
decoder applies. Conversely, the disjoint source pairs allow every original
tiling to be fused. No new global angular or packing theorem is inferred
from a forward picture alone.

The original internal ROOT contact is removed by fusion. A new bounded
exterior root predicate, its exact recurrence offset, and a check against
incidental event motifs are therefore mandatory. The first RESET digit's
east boundary survives in its fused pair. This source proof supplies pairing
and semantics only; actual union coordinates, side counts, simplicity and
observer recognition belong to the separately measured fusion implementation.
