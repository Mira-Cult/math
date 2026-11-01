# Full Collatz and recurrence in 30 polygons

**Thirty explicit unlabelled polygons, each with fourteen straight sides,
have a completed plane tiling satisfying the fixed recurrence below if and
only if every positive Collatz orbit reaches 1.** This is the 30-shape,
420-side construction shown in the two-page poster, not the earlier
34-shape construction.

This is a reduction, **not a proof of the Collatz conjecture**. Ordinary
plane tileability of these polygons is unconditional. The additional
recurrence condition is essential. The proof is ordinary mathematics
supported by exact finite checks, not a proof-assistant certificate.

## Read the proof

The [complete theorem and explicit 30-row coordinate table](manuscripts/polygon-v3-theorem.md)
is the main shareable proof note. Its supporting arguments are included here:

1. [24 binary digit rules and their arithmetic meaning](manuscripts/arithmetic-v3.md).
2. [Infinite carry streams and standardness before a reset](manuscripts/stream-arithmetic-v3.md).
3. [Intrinsic initialization and the completed-plane source frame](manuscripts/stream-frame-v3.md).
4. [Fourteen-side geometry and the converse for arbitrary contacts](manuscripts/geometry-v3.md).

No private repository, account, unpublished chat, or external seed is required
to read these proofs or run the checks. See [attribution](ATTRIBUTION.md),
[validation and limits](VALIDATION.md), and [source bindings](SOURCE.json).

## Exactly what the poster means

A tiling is a collection of translated and rotated copies of these polygons,
with disjoint interiors and union equal to the whole plane. Reflections are
forbidden. Edge-to-edge placement is not assumed. Nothing is preplaced.
The colors and names in illustrations are not matching rules.

In a positively oriented orthonormal frame `(u,v)`, define:

- `ROOT(p,u,v)`: at `p` a tile has consecutive genuine straight sides of
  lengths **38,43**, incoming in direction `v` and outgoing in direction
  `−u`, forming a convex right angle.
- `EVENT(q,u,v)`: the same type of corner, but lengths **32,13**, with
  **one and the same other polygon meeting the relative interiors of both
  sides**.

The exact bounded local specifications are in [observer-v3.txt](inputs/observer-v3.txt).
The acceptance condition is

```text
R(τ) ⇔ ∃ p,u,v: ROOT(p,u,v) and
                ∀ integer k≥1 ∃ integer j≥k:
                  EVENT(p + 13u + (66j−34)v, u,v).
```

The root and frame are fixed before the universal threshold. The theorem is

```text
(∀ positive n ∃ t≥0: Cᵗ(n)=1)
    ⇔ (∃ a completed legal plane tiling τ by the 30 polygons: R(τ)),

C(n) = n/2 when n is even, and 3n+1 when n is odd.
```

It is not a statement about every tiling, about ordinary tileability alone,
or about a finite illustrated window.

## Equivalent piece-counting formulation

The same theorem has the following simpler, equivalent formulation, using
whole polygon types numbered as in the poster and the theorem's tuple table:

> Full positive Collatz holds if and only if there exists a completed legal
> whole-plane tiling containing **a copy of piece 29 (ROOT)** and
> **infinitely many copies of piece 27 (RESET)**.

There is no need to specify “on that root's spine” in this formulation:
**once ROOT occurs, every copy of piece 27 is necessarily on its upward spine.**
This is a corollary of the included frame rules, not a change to the shapes.

**Proof of the reformulation.** The geometric converse decodes every legal
polygon tiling to one common oriented grid. In the
[30-type frame](manuscripts/stream-frame-v3.md#thirty-type-half-value-source),
each spine tile forces spine tiles at every site above it: its north color is
a parity color, and only spine tiles have a parity south color. At each of
those heights, its east carry forces a right-infinite row of digit tiles,
since only digits have a carry west color and every digit has a carry east
color. Thus two spine columns are impossible: above both starting heights,
the left column would force a digit at the right column's spine site.

ROOT likewise forces a spine at every positive height above itself. Every
spine must therefore lie in that same column. None can lie below ROOT, since
its upward continuation would force a spine at ROOT's site. Consequently all
spine tiles, including every piece 27, occur at positive integer heights
`j≥1` above this ROOT. This also rules out a second ROOT: a second column
would produce two spine columns, while a higher ROOT in the same column
would replace a forced spine. Infinitely many copies of piece 27 therefore
mean unbounded positive heights on the unique root's spine; conversely,
unbounded RESET heights give infinitely many copies of piece 27. These are
exactly the events counted by the original recurrence `R`. ∎

This counts **whole pieces of type 27**, not arbitrary occurrences of the
small 32/13 EVENT corner motif: that motif also occurs on digit piece 6.
The statement remains existential; it does not say that every continuation
of ROOT resets infinitely often. Quiet rooted tilings are still legal.

## Why the equivalence works

The polygon contacts force a common orientation and a translated 66ℤ² grid,
then exactly the finite source rules. An intrinsic ROOT initializes saved
odd target `n=1` and active value `v=1`. In an accepted tiling, the rows perform only

```text
(n,v)    → (n,2v)
(n,3w+1) → (n,w)       for positive odd w
(n,n)    → (n+2,1)     with an EVENT (RESET).
```

The first two transitions reverse ordinary Collatz edges. Thus a finite block
from active 1 to target n certifies that n reaches 1. Consecutive resets certify
1,3,5,… without skipping any odd target; every positive even integer reduces
to an odd integer by halving. A legal infinite binary stream need not encode
an ordinary integer, but the arithmetic proof shows that any row preceding
a later reset is standard. Unbounded future resets therefore rule out such
nonstandard exceptions in an accepted computation.

Conversely, if all positive Collatz trajectories reach 1, reverse the finite
trajectory for each successive odd target and concatenate these blocks with
resets. The source frame fills the remaining plane with background tiles, and
the geometric compiler gives a completed tiling. This is a whole-plane
existence proof, not an inference from ever-larger finite pictures.

## Reproduce the exact polygons and checks

Python 3.11 or later and its standard library suffice. From this directory:

```sh
python code/verify_v3.py
python -m unittest discover -s code -p 'test_*v3.py' -v
python code/build_v3.py --candidate parity30-profile14 --out /tmp/collatz30
python code/verify_v3_cells.py --certificate /tmp/collatz30/parity30-profile14-contact-certificate.json
sha256sum -c SHA256SUMS
```

The builder writes all 30 polygon outlines and the exact contact certificate.
It performs no Collatz search. Generated outputs are deliberately not committed.
The canonical [source alphabet](inputs/parity30-wang.json),
[selection hashes](inputs/selection-v3.json), and observer are included.
The 31-type source control retained in a shared proof and test module is not
the poster's selected set. No global minimum or record is claimed.
