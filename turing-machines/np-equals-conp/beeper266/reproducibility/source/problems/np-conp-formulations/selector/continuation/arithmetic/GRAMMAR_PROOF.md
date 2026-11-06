# Exact control preservation under grammar reassociation

This is an author proof for the selected use of `grammar_rotations.py`, adapted
from the PA lane's explicitly preserved source. The selection is an NP=coNP
producer-specific finite rotation plan. A PA plan, state count or mathematical
endpoint is not reused. All rotations are followed by a complete physical
build; smaller grammar counts alone do not establish a state saving.

## Finite representation and return paths

The compiler's finite acyclic binary grammar unfolds to an ordered list of
primitive occurrences. Repeated shared nodes are expanded separately for each
occurrence. An occurrence has a finite path whose root prefix is 110. The
inherited runtime represents this path on its control tape and implements:

- ordinary success: erase trailing ones and change the nearest remaining zero
  to one;
- failed DECNZ: skip that zero and return through the next zero;
- `_break.k`: the corresponding return with k skipped zeros;
- `_continue.k`: clear the suffix through k right-branch ones and restart the
  corresponding subtree.

These operations may return from the outer root to its beginning. The exact
root convention is included in the graph resolver, rather than dropping
edges that leave a convenient finite test prefix.

## The all-branch graph certificate

Each unfolded occurrence is numbered in left-to-right order. Resolving a
return path to the first leaf of the selected subtree produces a finite
directed graph with:

- one ordinary successor for each INC and event leaf;
- both the success and failure successors for every DECNZ;
- the resolved successor of every break and continue leaf.

The graph retains the physical-register primitive's exact name. Explicit
control leaves are recorded as jumps to their resolved occurrence. It is not
a bounded execution trace and does not infer a branch outcome from one run or
from an assumed value of a register.

A rotation changes an association `(a,(b,c))` to `((a,b),c)`, or the reverse,
at all occurrences of one chosen grammar pattern. Newly identical pairs may
reuse existing nodes. Acyclicity is checked while measuring and unfolding the
result. The finite plan is accepted only if the entire before and after graphs
are identical, including their occurrence counts, ordered primitive names and
all successors. The pre-rotation grammar, plan and graph identities are bound
separately from the final grammar. The inherited zero-entry certificate refers
to the pre-rotation grammar and is not relabelled as a certificate of a
different grammar.

Induct on primitive execution steps. Initially both executions select
occurrence zero with identical registers. Matching INC leaves perform the
same update; matching DECNZ leaves see the same register and take the same
one of the two certified successors. Matching event leaves emit once in both
executions. Matched explicit jumps have the same successor and no data effect.
Thus the induction maintains the occurrence and register equality and gives
the exact ordered event sequence for every natural-register configuration.
The graph relation is stronger than only preserving eventual silence.

## Physical progress and accounting

The new finite grammar is compiled by the same paid control-path engine and
register primitives. Its measured maximum path remains inside the counted
bootstrap's proved control space. Finite descents and returns through a
finite path complete; the shared selector and unary-register primitives
complete on every finite represented value. Each primitive step of either
graph therefore completes after finitely many physical steps. This rules out
an infinite administrative stutter before a later event or candidate check.

The event primitive and its physical adapter are unchanged. The final raw
table, exact B-exit quotient and exact event-colored quotient are regenerated
and checked in full. All resulting states, including the embedded grammar,
dispatch, scratch addressing, bootstrap and totalization, remain counted.
Reassociation does not provide a preloaded program or an external observer.

The selected graph equality is executable finite evidence for this fixed
producer. Independent review separately implements the inherited bit-path
semantics, checks every edge and replays the selected plan. Conventional
runtime proofs and cofinal-progress reasoning supply the unbounded conclusion;
neither these finite graphs nor a bounded literal run decide NP versus coNP.
