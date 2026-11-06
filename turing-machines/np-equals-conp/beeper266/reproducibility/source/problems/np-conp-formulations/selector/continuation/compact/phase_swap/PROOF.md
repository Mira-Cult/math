# Exact orientation swap through one zero work cell

This proof concerns the new lowering in [region.py](region.py) and its
complete fixed parent in machines/parent290 (historical reference: `machines/parent290/metadata.json`; outside this selected-only export).
It composes with the unchanged [291-state source theorem](../transfer328/PROOF.md).
The fresh completion to the selected 284-state table has its own
[composition proof](COMPOSITION.md), raw-preimage domain and event maps.
The parent and its completion are distinct complete constructions.

## Source and admitted boundary

[source.py](source.py) is byte-identical to
`transfer328/control/attempt_reset/source.py` at producer
`81147084e3d81219073ba6b8f0e6a3e3af8cf116`. Its SHA-256 is
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.
The exact byte comparison is part of check_swap.py (historical reference: `check_swap.py`; outside this selected-only export).
No source assignment, predicate, input order, acceptance attempt, event or
comparison changes here. The metadata's inherited `source_changed` flag
refers to the older compiler source baseline; `source_unchanged_from`
identifies the precise 291 producer comparison.

The only new lowering matches the exact simultaneous tuple assignment

```python
left, right = right, left
```

with two distinct names. There are two occurrences, one in each acceptance
phase, when the decoded relative turn bit is one. The source values of the
two simulated tape halves must be exchanged before the following write and
move. All other source variables must agree at the exit. In particular the
description, initial input, certificate enumeration master, expected result,
clock, remaining steps, write bit and decoded next state are preserved by
the swap itself.

Let the admitted values at its external entry be

\[
L=\ell,\qquad R=r,\qquad Q=0,
\]

where \(\ell,r\) are arbitrary natural numbers. The three logical carriers
are distinct. Here \(Q\) is the inherited `$micro.q` work carrier; it is not
an extra argument or a caller tag. The physical boundary relation also
includes the complete control path, head location, finite unary register
bank, positive one-run delimiters, zero reserve and all other live values.
The source's two call sites use the same lowerer and ordinary primitive ABI.

The entry-zero requirement concerns every **outside incoming edge** to the
region. It does not assert that Q remains zero when the first transfer's
loop header is revisited. On that internal backedge Q contains the portion
of L already transferred. The fresh abstract invariant must be checked on
the outside predecessor's branch-specific image. This distinction is
essential to the ownership proof.

## Three-transfer refinement for all naturals

The existing additive transfer `move(dst, src)` repeatedly applies DECNZ to
src and, on success, INC to dst. It maps
\((\mathrm{dst},\mathrm{src})=(a,b)\) to \((a+b,0)\), preserves every
other logical value, and terminates after \(2b+1\) retained primitive
applications. Its last application is the failing zero test. Each positive
iteration decreases the finite source by one.

The exact matched assignment becomes

```text
move(Q, L)
move(L, R)
move(R, Q)
```

The three boundary valuations are respectively

| Boundary | L | R | Q |
|---|---:|---:|---:|
| External entry | \(\ell\) | \(r\) | 0 |
| After first transfer | 0 | \(r\) | \(\ell\) |
| After second transfer | \(r\) | 0 | \(\ell\) |
| Sole exit | \(r\) | \(\ell\) | 0 |

The second and third destinations are zero because the preceding transfers
established those zeros. No snapshot is lost. Every carrier other than L,
R and Q is untouched, and Q is restored to its required zero value. The
exit therefore agrees with the simultaneous source assignment on the
entire source store and scratch interface.

This is a complete local refinement for arbitrary \(\ell,r\), including
either or both zero, all-one finite binary tape encodings and repeated
turns. Its total retained primitive count is exactly

\[
(2\ell+1)+(2r+1)+(2\ell+1)=4\ell+2r+3>0.
\]

There is no event, source escape or nonlocal return within the region.
The only external exit follows the final failing DECNZ, after Q has become
zero. Each inherited primitive has a positive finite physical segment on
every admitted finite bank, so the whole swap has a positive finite physical
realization. A stalled scratch restoration cannot create eventual silence.

After the fixed control rewrites the actual retained graph contains two
six-row regions, at rows 71–76 and 162–167. These are measured locations,
not recognition assumptions. check_swap.py (historical reference: `check_swap.py`; outside this selected-only export) locates the
recurrence by operation identities and every edge, checks all outside
ingresses and exits, and executes those actual rows. Each recurrence is

```text
0: DECNZ L -> 1 on positive, 2 on zero
1: INC Q   -> 0
2: DECNZ R -> 3 on positive, 4 on zero
3: INC L   -> 2
4: DECNZ Q -> 5 on positive, exit on zero
5: INC R   -> 4
```

The row numbers are local to this retained graph, not numerical binary
state identities. There is one outside ingress from the turn HALF at each
site and one outside exit to the following arithmetic. The untaken turn
branch bypasses the complete swap without modifying Q.

## Fresh allocation and every intermediate ownership obligation

The new lowering emits only the inherited INC and DECNZ operations. It
introduces no atomic MOVE instruction and no new physical kernel. The
source allocator still sees the simultaneous swap of two live source
values, so it keeps L and R distinct. Its reserved arithmetic carrier Q is
not a source-variable colour. The lowerer asserts logical distinctness;
the actual mappings are

| Value | Allocated logical carrier | Physical class |
|---|---|---|
| L | `$liveframe.0.6` | `$coalesced.8` |
| R | `$liveframe.0.7` | `$coalesced.1` |
| Q | `$micro.q` | `$coalesced.10` |

The full allocation, contextual reduction, finite control plan, projection
and coalescence certificates are regenerated. The chain is 22 original
logical/arithmetic coordinates to 19 allocated registers, 15 projected
logical coordinates and 12 physical classes. It removes the second generic
tuple snapshot register. The grammar retains 185 primitive/event rows,
with 184 reached register operations checked by the sharing certificate,
81 explicit zero-peer obligations and 362 abstract postfixed edges.

As before, each physical class represents the sum of its logical ghost
values. Every non-operated member of a class must be zero at each reached
operation. In particular Q shares its class with `$pool0.tmp0`; that peer
must be zero throughout each operation of the swap, and Q must be zero
whenever the peer is used elsewhere. The fresh invariant checks this over
the actual intermediate INC/DECNZ states. The source-level swap equation
alone would not license this sharing. L, R and Q remain different physical
classes throughout the region.

Both clock and certificate-seed lowerers remain unchanged and retain their
own explicit master-interference edges. Their entry scratch and restored
master exits are re-established in the new whole-program invariant. The
consuming-guard lowerer and the parser/parity/record lowerers remain unchanged.
The lowerer context preserves maximal unmatched statement spans so it does
not silently alter those compound recognizers. Its fixed context ordering
is part of [build.py](build.py), and reproduction checks the resulting bytes.

This proof does not inherit an aliasing permission from the rejected
historical 353-state decoder. No source result is cleared early here before
its old value has been consumed. All three transfer stages and their work
lifetimes are explicit in the emitted primitive graph and fresh invariant.

## Complete parent and physical composition

The new ordinary parent has 294 raw states, 291 B-companion states and 290
marked states. Every state has both binary rows and every target exists.
The marked table has 580 rows and SHA-256
`d69abfcee4b8dd4071409982628adb7a8319f82a571ea7cedb87309c8ba586af`.
The B table has 582 rows and SHA-256
`3a99acf406c7a178e9e85d523e216c2b3345b231ed65ad22197d9eed1fb718ea`.
The raw table hash is
`e15e15e431945919a06bdd265ebe1ee6fc81c44cae5618d89a9d394148ea4440`.
The fixed recipe includes all source, plans and group inputs; discovery is
separate in measure.py (historical reference: `measure.py`; outside this selected-only export).

Against the ordinary complete 297-state sequential-reset parent, this lowers
the marked count by seven. Four are in the measured arithmetic/control
partition, which changes from 164 to 160, and three are elsewhere. The bank
changes from 13 physical classes to 12. These are complete integrated counts,
including both acceptance phases, all caller entry and exit paths, input
parsing, reset, clock and certificate-capacity construction, both comparison
outcomes, outer enumeration, event adaptation and blank initialization.
There is no supplied program or tape alphabet parameter outside the count.

The binary bank and existing physical kernels have the same contracts as
the [native proof](../compiler/native/PROOF.md) and
[bank proof](../compiler/native/BANK_PROOF.md). Arbitrarily long data travel
uses their finite sweep controllers. The shorter finite grammar has maximum
leaf length 55; its return-dispatch bound must be derived from its own
maximum zero-count, not copied from the old table. The physical review checks
the actual retained kernel rows and any changed dispatcher parameter.
Fresh raw quotients, semantic row exclusions, all raw preimages and event
maps are obligations of the separate 284 completion, not consequences of
this local swap equation.

At source boundaries this is the identical normalized NP=coNP source. Its
independent-write, overlapping-record, relative-direction semantics, virtual
zero tails, protected certificate masters, ignored positive input suffixes,
reference witness coverage, exact `(n+1)^j` candidate bound and empty-prefix
cases all remain those of the inherited complete theorem. The swap neither
changes certificate enumeration nor removes the expensive numerical clock
and witness-capacity builders. Every finite comparison still terminates.
The source event order is identical to the 291-state source while physical timing changes.

Thus positive finite segment composition preserves an infinite physical run
in both cases and exactly the source events. After the separately checked
completion/event maps, finite designated events mean NP=coNP; infinitely
many events, the established 1-acceptance convention, mean NP differs from
coNP. Silence arises from continued correct comparisons. No finite replay
establishes eventual silence.

## Evidence and review boundary

The author receipt (historical reference: `checks/swap.json`; outside this selected-only export) records 524 actual retained-row
fixtures, 110,616 primitive applications and all three transfer boundaries.
It covers zero inputs, unequal values, equal values, long finite tape-half
values, preservation of every other physical class and exact primitive
counts. Six malformed matcher inputs and six deliberately damaged region
or entry cases are rejected. These are prepared primitive-boundary checks;
they are not literal binary runs or blank-start evidence.

reproduce_parent.py (historical reference: `reproduce_parent.py`; outside this selected-only export) performs a fixed-plan rebuild and
compares all 38 canonical artifacts byte for byte. Its
receipt (historical reference: `checks/reproduction.json`; outside this selected-only export) records the complete count and hash.
Source mathematical and binary implementation reviews are independent of
this author work and are bound to a later immutable producer commit in the
review directories. Those reviews, literal blank runs, event-map checks,
reviewer identity and publication bindings are reported separately. Internal
nonauthor model review is not external human certification or Lean checking.
