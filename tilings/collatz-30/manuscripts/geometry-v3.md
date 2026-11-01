# Fourteen-side orthogonal compiler

This manuscript proves the geometric compiler used by the v3 candidates. Its
status is **ordinary mathematical proof with reproducible exact finite
certificates**. The unit-cell verifier is separately implemented, but that fact
does not constitute an independent mathematical review. Review bindings are
recorded separately after the scientific producer is frozen. Nothing here is
kernel checked, a minimality theorem, or by itself a Collatz equivalence.

The canonical implementation is [geometry_v3.py](../code/geometry_v3.py), with
the exact certificate verifier [test_geometry_v3.py](../code/test_geometry_v3.py).
The generic integer quarter-turn and rectangle utilities are imported from the
unchanged reviewed [v2 compiler](../code/geometry_v2.py). The source/frame and
recurrence implications belong to their own manuscripts.

## Model and compiler theorem

Use a finite collection of simple closed polygons with disjoint interiors and
union equal to the whole Euclidean plane. Translations and arbitrary rotations
are permitted; reflections are not. **Edge-to-edge placement is not required.**
In fact, the intended placements include vertices on the interior of another
polygon's longer side.

For either parameter tuple in the table below, compile any finite set of distinct
Wang four-tuples with the stated horizontal and vertical palette sizes. Every
legal completed polygon tiling has one common orientation and the macro-origins
of its tiles are exactly a translate of the square lattice of spacing \(L\) in
that orientation. The polygon at each site decodes uniquely to its source
four-tuple, and adjacent source colors match. Conversely, every completed Wang
tiling gives a completed tiling by the literal polygons. Both statements hold
without a supplied seed, coordinate origin, global direction, or boundary.

| Palette | \(L\) | \(d\) | \(f\) | \(t\) | \(u\) | Coordinates | Core area |
|---|---:|---:|---:|---:|---:|---|---:|
| Selected: \(H=8,V=6\) | 66 | 19 | 13 | 19 | 25 | integers in \([-19,79]\) | 4,170 |
| Retained: \(H=10,V=5\) | 75 | 23 | 17 | 23 | 28 | integers in \([-23,92]\) | 5,380 |

For other parameter tuples, the same argument applies when the structural
inequalities below hold and `full_certificate` passes its literal verifier.
The deterministic default for an unlisted palette is only a candidate until
that certificate is checked; it is not an unqualified uniform bound.

## Exact fourteen-vertex formula

Horizontal colors on east/west faces are coded by integers
\(e,w\in\{0,\ldots,H-1\}\). Vertical colors on north/south faces are coded by
\(n,s\in\{0,\ldots,V-1\}\). The code assignment orders colors by descending
frequency among the supplied four-tuples, breaking ties by their literal
representation. The assignment, source tuples, and integer vertices are all
included in the compiled output.

In counterclockwise order the vertices of \(P(n,e,s,w)\) are

\[
\begin{aligned}
 &(0,-d),\ (t+s,-d),\ (t+s,0),\ (L+f,0),\\
 &(L+f,u+e),\ (L,u+e),\ (L,L),\ (t+n,L),\\
 &(t+n,L-d),\ (0,L-d),\ (0,u+w),\ (f,u+w),\\
 &(f,0),\ (0,0).
\end{aligned}
\]

The conditions used throughout are

\[
0<f<t,\quad t+V-1<L,\quad 0<u,\quad u+H-1<L-d,
\quad d>0,\quad d\ne f,
\]

and

\[
A=L^2-d(V-1)-f(H-1)>
\max\{d(V-1),f(H-1)\}.
\]

Start with the square \([0,L]^2\). Add a south rectangle
\([0,t+s]\times[-d,0]\) and an east rectangle
\([L,L+f]\times[0,u+e]\). Remove the north rectangle
\([0,t+n]\times[L-d,L]\) and west rectangle
\([0,f]\times[0,u+w]\), with the natural boundary closure. The inequalities
separate the north and west cuts and leave positive-width corridors connecting
the interior. They also separate the two protrusions. Tracing the boundary gives
exactly the fourteen vertices above, with no repeated vertex or crossing.
Every side has positive length and every turn is \(90^\circ\) or
\(270^\circ\); none can be removed by collinearity simplification. This is a
simple polygon with connected open interior and exactly **fourteen genuine
straight sides**, not a schematic square with uncharged profiles.

Every polygon has bounding-box width \(L+f\) and height \(L+d\). Since
\(d\ne f\), no two members of this family can be quarter-turn congruent.
Every member contains its bounding box's lower-left corner \((0,-d)\), but
does not contain its upper-right corner \((L+f,L)\). Thus no two can be
half-turn congruent either. For equal orientations, the four profile endpoints
recover \((n,e,s,w)\). Distinct oriented poses therefore denote distinct
physical copies unless their orientations, translations, and source tuples
agree. The implementation also compares all literal normalized oriented
outlines in each selected set.

## Common core, envelope, and two rejection lemmas

Every prototype contains the closed mandatory core

\[
C=P(V-1,0,0,H-1)
\]

and lies within the closed envelope

\[
E=P(0,H-1,V-1,0).
\]

The core area is \(A\) above. Its connected interior is not needed for the
overlap lemma; the connected open interior of every complete tile is needed
for the cavity lemma.

**Overlap rejection.** If two distinct required poses of \(C\) overlap in an
open rectangle, the corresponding physical tiles cannot both occur. The
certificate supplies the two poses and a positive-area integer rectangle
inside both cores. It never rejects merely because boundaries meet.

**Cavity rejection.** Consider finitely many required tile poses. Let \(K\)
be the union of their closed mandatory cores. Suppose a bounded component
\(U\) of \(\mathbb R^2\setminus K\) has area less than \(A\), and contains a
nonempty open rectangle outside every envelope of those required tiles. Then
the required poses cannot occur in any completed tiling.

To prove the second statement, choose a point of that open rectangle in the
interior of some tile not among the required copies. Such a point exists:
local finiteness, proved below, makes the tile boundaries a finite union of
segments in a compact subrectangle, which cannot cover its interior. The new
tile's connected open interior avoids \(K\), so it lies entirely in \(U\).
It has area at least \(A\), contradicting \(\operatorname{area}(U)<A\).
A zero-width contact cannot give its open interior a passage through a closed
core boundary.

All required poses are integer quarter-turn poses. The producer finds cavities
by a coordinate-compressed rectangular grid containing every core and envelope
boundary. The certificate records all rectangles of the component, its area,
the required poses, and an uncovered rectangle. The independent unit-cell
checker does **not** call that flood-fill or the producer's overlap routines.
It checks every cell of the component is outside every core, every neighboring
cell on its boundary belongs to a core, its cell graph is connected, the area
is smaller than \(A\), and every cell of the specified uncovered rectangle is
outside all required envelopes. These facts alone prove the cavity rejection.

## Exhaustiveness despite arbitrary rotations and partial-edge contacts

First, every legal tiling by a finite set of these polygons is locally finite.
Choose a positive radius \(\rho\) such that each prototype contains a disk of
radius \(\rho\), and a uniform diameter bound \(D\). A tile meeting a compact
set has its chosen disk inside the \(D+\rho\) neighborhood of that set. The
disjoint disk interiors give a finite area bound on the number of such tiles.

The graph joining tiles that share a positive-length boundary segment is
connected. Join interior points of any two tiles by a generic finite path that
avoids all vertices in its compact neighborhood and crosses edges transversely.
Local finiteness reduces this to finitely many exclusions. Each crossing gives
a positive-length edge contact. All sides in any one tile use two perpendicular
directions; a segment contact aligns those directions modulo \(90^\circ\).
Consequently, after fixing the frame of one tile for the proof, every tile in
the plane has one of four relative orientations. This choice is a proof
coordinate, not a supplied seed or condition on the tiling.

At a reflex vertex of a tile the remaining angle is exactly \(90^\circ\).
Every incident tile has angle at least \(90^\circ\); a point in a straight
side has angle \(180^\circ\). Exactly one other tile therefore supplies one
convex \(90^\circ\) vertex. The complete pool of possible convex vertices in
our family is

\[
\begin{split}
\mathcal V={}&\{(0,-d),(L+f,0),(L,L),(0,L-d),(0,0)\}\\
&\cup\{(t+c,-d),(t+c,L):0\le c<V\}\\
&\cup\{(L+f,u+c),(0,u+c):0\le c<H\}.
\end{split}
\]

For a reflex target \(z\), every filler is among
\((k,z-R_kv)\), with \(k=0,1,2,3\) and \(v\in\mathcal V\). Including
poses whose wedge points the wrong way is harmless: this is a finite
superset, and the rejection proof must eliminate every unintended survivor.
Neither an edge-to-edge hypothesis nor a pre-existing macro-grid is used.

## The three certificate stages

The exact dependency order is west jointly, north singly, east/south jointly.
Previously proved offsets are applied in each candidate's own rotated frame.
Only one step of each previous offset is used. Coincident poses are coalesced;
different poses have different physical copies by the preceding congruence
argument.

1. **West.** For every possible west color \(w\), fill both reflex vertices
   \((f,0)\) and \((f,u+w)\). Enumerate the full candidate pool at each, then
   every pair of surviving poses. Include the original tile and both fillers
   in each rejection test. The sole surviving pair consists twice of the
   same-orientation pose \((-L,0)\). Thus every tile has that west neighbor.
2. **North.** For every north color \(n\), fill \((t+n,L-d)\). Include the
   mandatory west neighbor of the original tile and of the candidate filler.
   Only the same-orientation pose \((0,L)\) survives. The north rule is now
   universal.
3. **East and south together.** For every pair \((e,s)\), fill
   \((L,u+e)\) and \((t+s,0)\). Include the original tile, both fillers, and
   each tile's already mandatory west and north neighbors. Enumerate the
   Cartesian product of the two surviving candidate sets. The sole surviving
   pair is \(((0,(L,0)),(0,(0,-L)))\). Thus both remaining neighbor rules are
   universal.

The joint stages are essential: neither of the east and south corner tests
alone forces its intended neighbor. The relevant alternative fillers can be
individually nonoverlapping, but cannot coexist around the original tile.
This is a simultaneous local constraint, not a presumed construction order.

For the selected \(H=8,V=6\) parameters, the literal certificate covers 29
single-corner cases and 56 paired cases. It rejects 7,395 cases in total:
6,651 by positive-area core overlap and 744 by bounded cavities. The verifier
reconstructs the complete pose universes and Cartesian products independently,
checks exact set equality against rejection and survivor records, and admits
each universal rule only after its preceding stage has passed. Missing a case
is a verification failure. The retained \(H=10,V=5\) parameters receive their
own full certificate, not an inference from the selected palette.

## From four universal neighbors to the whole-plane grid

Starting at any tile, iterate the four universal same-orientation offsets.
There is a required tile at every point of its translated \(L\mathbb Z^2\)
grid. Reaching a position in two ways gives the same physical copy: otherwise
the two common cores at that position would overlap in positive area.

It remains necessary to exclude extra tiles between these forced copies.
Let \(P_0=P(0,0,0,0)\). Its lattice translates partition the plane: the east
and south rectangles are transfers from their adjacent squares and exactly
fill the paired west and north removals. Equivalently, its integer unit cells
have exactly one representative of every residue class modulo \(L\) in each
coordinate. The source verifier checks this literal finite identity.

Relative to \(P_0\), the core removes precisely two extra rectangles,

\[
B_N=[t,t+V-1]\times[L-d,L],\qquad
B_W=[0,f]\times[u,u+H-1].
\]

The union of all forced closed cores leaves only the interiors of translates
of these rectangles. The structural inequalities make them pairwise separated
components, including across neighboring macro-cells. Their areas are
\(d(V-1)\) and \(f(H-1)\), both smaller than \(A\). An additional tile's
connected open interior would have to lie in one such component, contradicting
its minimum area. Thus every tile is one of the forced lattice copies. There
are no fault-line, displaced-phase, rotated-background, or extra fractional
tile exceptions to this compiler theorem.

At neighboring sites, an east code \(e\) and west code \(w\) differ only in
the seam rectangle \([L,L+f]\times[u+\min(e,w),u+\max(e,w)]\). If \(e>w\)
there is positive-area overlap; if \(e<w\) there is a gap. The separation
inequalities exclude envelopes from other lattice sites from this middle seam.
Hence \(e=w\). The north/south argument is identical with the other profile.
Every completed geometric tiling therefore decodes to a genuine completed Wang
tiling, up to one global translation and rotation.

Conversely, matched neighboring source colors make each rectangle transferred
across a seam exactly fill its partner's dent. The original square partition
then verifies disjoint interiors and coverage everywhere. This constructs the
entire plane, not merely a forward computational patch.

## Two genuine sides suffice for each selected geometric recognizer

For any compiled finite palette, `convex_pair_matches` enumerates every convex
vertex and the ordered lengths of its two complete adjacent genuine sides.
It verifies the following recognizers directly against every literal polygon.
They inspect geometry, not source labels or arithmetic.

At an east-cap corner \((L+f,u+e)\), the incoming side points north with
length \(u+e\), then the outgoing side points west with length \(f\). These
two full sides share the east neighbor. In the selected thirty-shape set the
RESET east color has code seven, giving the ordered pair **\((32,13)\)**.
It occurs in source types 6 and 27; only type 27 is the RESET spine in a
rooted spine column. That contextual classification is a source/frame proof
obligation, not part of this local recognizer.

At the northeast corner \((L,L)\), the incoming northward side has length
\(L-u-e\), followed by a westward side of length \(L-t-n\). The ordered
pair for the ROOT colors is **\((38,43)\)**. Exact enumeration finds it only
in source type 29. The recognizer does not require the two sides to have the
same neighboring tile; their other contacts may include partial edges.

Both events are two-side convex-corner predicates. A disk centered at the
corner with radius one more than the larger side length contains the complete
two sides and neighborhoods of both endpoints, so maximality and the convex
turn can be inspected within a precisely bounded patch. The paid radii are 33
for the event and 44 for ROOT. All coefficients and lengths are integers.

In a common frame \((\mathbf u,\mathbf v)\), if \(p\) is the ROOT corner,
the corner for a RESET spine at row \(j\) lies at

\[
p+13\mathbf u+(66j-34)\mathbf v.
\]

This fixed offset is charged explicitly; the global recurrence still has to
require unbounded row indices in this same intrinsic column. An arbitrary
infinite collection of matching corner motifs elsewhere is not acceptance.

## Measured cost, scope, and reproducibility

| Actual uniform source set | Shapes | Sides per shape | Total sides | Maximum absolute coordinate | Signed coordinate bits | Arithmetic coordinate field |
|---|---:|---:|---:|---:|---:|---|
| Thirty-type parity-spine source | 30 | 14 | 420 | 79 | 8 | integers |
| Thirty-one-type retained source | 31 | 14 | 434 | 92 | 8 | integers |

These are completed measured compiler geometries. Establishing their claimed
recurrent Collatz problems additionally requires the separate arithmetic,
frame, acceptance, and constructive-completeness proofs. Any fused variants
are measured and proved separately; no fused count is inferred here.

Translations-only tilings form a valid restricted variant of the same
equivalence. The result does not establish a reflection-allowed compiler, nor
an edge-to-edge version. No extra matching rules, encoded real constants,
hidden polygon primitives, or free geometric decoder are used.

From the repository root:

```sh
python -m unittest discover -s problems/collatz-polygons/code -p test_geometry_v3.py -v
python problems/collatz-polygons/code/geometry_v3.py --h 8 --v 6 --out /tmp/endpoint14-selected.json
python problems/collatz-polygons/code/geometry_v3.py --h 10 --v 5 --out /tmp/endpoint14-retained.json
```

The eight research tests validate both literal certificates after sorted-JSON
roundtrip, the actual thirty- and thirty-one-shape outlines, all counted sides,
simplicity, raster agreement with the rectangle-transfer formula, the periodic
core partition, and the exact two-side observers. Mutations removing a pose
case, substituting a false overlap, supplying a false cavity, violating a structural parameter hypothesis, or supplying nonintegral pose/box data are rejected.
These finite checks discharge explicit finite obligations in the preceding
ordinary proof; bounded search alone is not its infinite conclusion.

The reduction from twenty to fourteen sides comes from joining the four
arithmetic color rectangles to macro corners, thereby merging six genuine
straight sides. Its additional proof cost is the cross-face joint constraint
and exact cavity witnesses. Parameter search is not a minimality argument.
