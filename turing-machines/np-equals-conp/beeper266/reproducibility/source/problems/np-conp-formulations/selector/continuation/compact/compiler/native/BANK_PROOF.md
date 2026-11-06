# Projection of an unused zero bank

`bank_projection.py` runs after the contextual zero-entry and optional
finite-control rewrites, immediately before physical generation. It removes
only source-store coordinates absent from every retained ordinary or native
primitive. This is a new representation proof; it is not an all-row quotient
of the previous literal Turing table.

Let G be the complete finite grammar at that point, with allocated register
set R. Let A contain each register named by any INC, DECNZ, or native half
primitive in any reachable grammar node, including both branches of every
conditional. The producer checks that every such operand belongs to R.
If A is empty, retain the old first register to satisfy the fixed bootstrap's
one-register ABI. Every removed coordinate is therefore unreferenced in G.

The admitted source entry has all registers zero. Induct on grammar steps.
Each primitive operates only on coordinates in A, and control primitives
modify none. Every removed coordinate remains zero forever. The projection
onto A thus preserves every retained primitive input/output, both outcomes
of every ordinary or native conditional, and every source event. The inverse
interpretation adds zero in each omitted coordinate. No two retained cells
are identified. Primitive and control order are exactly the same.

The source-liveness and contextual certificates remain certificates over
their original carrier, usually 27 cells. `pre-control-grammar.json` records
the contextual output when control rewriting is used. The finite-control
plan ends at `pre-projection-grammar.json`, still with the original carrier.
The projection certificate binds that grammar to the emitted final grammar;
their nodes and root are identical and only the register list differs.
All omitted cells and their zero interpretation, old-to-new indices, exact
retained primitive positions, and native operand order are recorded. A
source observation of an omitted coordinate is interpreted as zero, not
looked up as an existing physical block.

Native operands are selected from the actual retained native tags, rather
than the earlier lowering inventory. They are placed first, preserving the
relative order of their old cells; all other retained cells follow in their
old order. This handles reduced fixtures in which a former native invocation
was eliminated. It is another finite layout permutation with no aliasing.

Before physical generation the old register transition templates are
discarded and every retained ordinary entry/index row is rebuilt for its
new position. The unchanged framework, shared selector and event adapter
are then generated against this exact inventory. In native mode the native
entries/selector are also generated from the filtered prefix. The native
kernel and its full unary-bank contract are unchanged. Each old active value
is represented by a distinct block at its new index; deleted zero blocks
are no longer part of the active carrier. Trailing zero reserve blocks are
allowed by both physical engines' existing invariant.

The paid blank initializer still provides an all-zero bank with sufficient
finite capacity. This mathematical fact does not transfer an earlier
literal trace: each selected projected table receives its own fresh blank
startup verification. All preparation gaps, source paths and register counts
remain within the existing paid capacities. Every ordinary and native
primitive terminates on a finite admitted bank. The projection therefore
preserves cofinal source progress and the complete ordered source event
sequence. Subsequent B-exit adaptation, ingress shift and exact event
quotient preserve finite versus infinite events as before.

The complete native and ordinary builds have separate literal identities
and counts. No saving is inferred merely by subtracting the number of
removed coordinates: `build_projected.py` generates and counts every row.
Finite fixture checks and independent physical review are separate from
this proof; no bounded run establishes eventual silence.
