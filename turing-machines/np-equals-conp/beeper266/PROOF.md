# Proof and compression guide for the 266-state machine

The 266-state machine implements the same complement-verifier search as the
284-state machine. The [284-state proof guide](../beeper284/PROOF.md)
explains the mathematical reduction to NP = coNP. The smaller table requires
new conventional source and physical arguments: the 284-state Lean endpoint
does not transfer automatically across these changes.

This guide explains the changes and what each proof must preserve. The
canonical producer argument, including the unchanged predecessor contracts,
is retained in
[`control_regions/PROOF.md`](reproducibility/source/problems/np-conp-formulations/selector/continuation/compact/control_regions/PROOF.md).

## 1. Preserve the complement search

Write `N=N(i)` and `D=D(i)` for the marker/payload parser's results. The
reference returns `R=A(D,0,N)`. The candidate returns
`Q=A(j,i,(N+1)^j)`. Both predicates quantify existentially over their complete
finite certificate domains. The candidate sees the entire original input,
even when the reference parser ignores a high suffix.

The search continues silently exactly when `R ≠ Q`. Both `R=Q=0` and `R=Q=1`
are counterexamples. A good fixed candidate exists exactly when NP = coNP.
Source progress and literal finite-segment progress are needed so that the
machine cannot appear silent merely by stalling inside a comparison.

## 2. Reuse carriers only after their old values are dead

The selected source is
[`reuse_clock_roles.py`](reproducibility/source/problems/np-conp-formulations/selector/continuation/compact/control_regions/sources/reuse_clock_roles.py),
SHA-256 `0b0bf4045fec4392de646047d65db90f1959b8086156a418aa40f45e355bb11b`.

After the reference bit returns, its description and time carriers are no
longer needed for that reference evaluation. The source changes their roles:

```python
e = n
n = (e + 1) ** j
e = j
```

At these source boundaries `(e,n)` becomes `(N,N)`, then `(N,(N+1)^j)`, then
`(j,(N+1)^j)`. The candidate therefore has precisely the original description,
input and clock. Both acceptance bodies can now use the same operand positions.

The proof compares candidate attempts in their actual descending certificate
order and each attempt's simulated steps. It preserves the original input,
description, tape halves, state, remaining time and acceptance bit. It does
not assert that two differently allocated internal stores are equal after
every source statement.

This matters at the clock entry. The actual lowering of `e=n` consumes the
dead old `n` while moving it into `e`, taking `(n,e,T)=(a,b,0)` to `(0,a,0)`.
The new fourteen-row clock therefore receives a proved-zero output carrier.
It does not inherit the previous clock's arbitrary-stale-output contract.
The restoring `e=j` copy preserves `j` and clears its work. Every intermediate
store in the orientation swaps also retains the necessary ownership and
zero-work conditions.

The next comparison resets the changed roles before reading them, so the
source equivalence extends to the unbounded search. Empty parsed prefixes
still give candidate clock one. The source does not replace a real high input
suffix by zero or replace either existential test by one certificate.

## 3. Specialize nine occurrences, not every use of a shared node

Some zero tests can be removed because their operands are zero whenever that
particular source occurrence is reached. A shared grammar node may also be
called elsewhere with a nonzero operand; replacing all its uses would be
unsound.

The selected transformation first distinguishes occurrences by their full
paths. An inductive abstract invariant tracks zero, one, and values at least
two for every logical register. It checks entry and every admitted outgoing
edge, including both DECNZ outcomes and all native HALF parity cases. The
selected instance has 303 input occurrences and 391 checked invariant edges.
Exactly nine DECNZ occurrences have the required singleton-zero entry mask.

At each such occurrence, decrement-on-zero preserves the store and takes its
false lexical return. Replacing it by that return preserves the next source
occurrence and emits no event. Reinterning the expanded tree and checking the
finite cleanup provides exact successive control bindings. Unselected uses,
including nonzero uses of a formerly shared node, retain their original work.

The occurrence count and certificate are properties of this new source.
The earlier eight-occurrence precursor's proof is not silently relabelled as
the nine-occurrence certificate.

## 4. Pay for control geometry and physical storage

The control layout preserves every retained primitive and both branches of
every retained test. Its finite control check rejects all jump-only cycles.
Each physical scan and return has a finite delimiter/rank argument. Together
these prevent a new infinite administrative-only loop between comparisons.

The new layout shortens the maximum prepared terminal path from 56 to 29.
It still needs a **seven-state** return detector because a prepared path can
contain six consecutive zeroes. Those states are counted. No direct state
saving is inferred from the shorter path length.

The new allocation uses 19 allocated carriers, 15 projected carriers and
twelve physical register classes. A physical class represents the sum of its
logical ghost values. At each operated member, the proof must show that every
other member of its class is zero. The selected source has 188 checked
register operations and 85 explicit zero-peer sites. Reusing a carrier is
justified at its phase boundary and at intermediate transfers, not by the
final store alone.

All 1,909 initialized fields, the bootstrap writer, selectors, native HALF
implementation, clocks, certificate enumeration, resets and event adapters
are paid. A register model with fewer classes is not itself a smaller binary
machine.

## 5. Completion and exact events

The selected table is obtained from fresh physical rows and fresh maps.
Only reads excluded by the all-natural admitted-domain invariants may be
changed during completion. Every raw preimage of each excluded quotient row
must be checked; the absence of a read in a finite trace is insufficient.

Ordinary and event-aware quotient equations cover both reads of every state,
with complete destination closure and L/R moves. The selected marked table
has exactly one event row, `104 1 0 L 1 1`. Its B-exit companion observes the
corresponding exit one transition later. This keeps event polarity and state
counts separate.

The final disjoint state inventory is:

| State origins | Count |
| --- | ---: |
| Compiled arithmetic and control | 154 |
| Ordinary operation entries | 24 |
| Operand selectors | 24 |
| Native HALF entries | 4 |
| Native HALF kernel | 13 |
| Native HALF selection and preparation | 5 |
| Mixed HALF kernel, selection and engine class | 1 |
| Remaining engine and dispatch | 27 |
| Return detector | 7 |
| Blank bootstrap | 4 |
| Mixed bootstrap and totalization class | 1 |
| Event adapter | 1 |
| Mixed event and engine class | 1 |
| **Total** | **266** |

The last step from the reviewed 271-state predecessor removes six control
states but pays one extra return-detector state. The preceding return and
dispatch changes account for the rest of the eighteen-state saving from 284.

## 6. Evidence and review boundaries

The conventional proof composes source equivalence, admitted control
specialization, fresh storage relations, terminating physical segments,
blank initialization, and exact event maps. Separate internal model reviews
examined source/control and physical obligations at the immutable producer
revision. They are not a Lean proof or external human certification.

Upstream literal tests reached source entry after 89,836,674 transitions,
then observed three marked events and completed silent comparisons. Independent
engines compared full configurations, and prepared fixtures covered cases
not seen in that prefix. The observed blank prefix includes `(1,1)` refutation;
`(0,0)` is covered by the source argument and separate tests, not claimed as
observed in that blank prefix. These are finite regression checks.

For a skeptical review:

1. Verify the exact source, tables, producer revision, and hashes.
2. Recheck both acceptance predicates, full input bits, candidate order,
   certificate bounds, and both equal-bit refutations.
3. Trace the consuming and restoring copies into the actual new clock ABI.
4. Check all nine occurrence paths against the complete invariant, including
   fresh cleanup and control-layout bindings.
5. Check peer-zero premises at every operated class member and intermediate
   transfer, not just comparison boundaries.
6. Check every physical row and completion preimage, literal blank entry,
   positive finite progress, and event correspondence.
7. Reproduce the fixed construction and finite controls, keeping their scope
   separate from the all-time conventional argument.

See [VERIFICATION.md](VERIFICATION.md) for public-package reproduction status.
