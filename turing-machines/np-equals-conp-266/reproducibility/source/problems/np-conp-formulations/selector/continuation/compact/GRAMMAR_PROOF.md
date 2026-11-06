# Finite administrative control contraction

This is a conventional preservation proof for `weak_grammar.py`, `grammar.py`
and the fixed five-move `grammar-plan.json`. The coordinator authored these
files. Independent review, literal simulations and immutable producer bindings
are recorded separately. No proof-assistant certification is claimed.

## Domain and the preceding certificate

The input is the finite binary control grammar produced by the inherited
natural-number compiler and its checked zero-entry transformation. A leaf is
an INC, a conditional DECNZ, a beep, or a numbered lexical break/continue.
An internal pair pushes the corresponding left/right path bit. The inherited
runtime executes the resulting path using its paid binary dispatcher.

The zero-entry certificate ends at `pre-control-grammar.json`, after the
separately proved blank bootstrap has initialized every source register to
zero. It does not by itself certify the rewritten final grammar. The new
`control-certificate.json` binds that intermediate grammar, the final
`grammar.json`, the exact plan and their source identities. The selected
producer checks that the intermediate grammar hash is precisely the output
hash of the zero-entry certificate.

## A finite graph with both conditional outcomes

Unfold the finite grammar from its root, with initial physical path `110`.
Every leaf occurrence has its own ordered index, even when an internal node
is shared. For an ordinary return, remove the nearest pending left edge and
enter the corresponding right subtree. A failed DECNZ skips one additional
such continuation. The numbered break and continue conventions similarly
determine their explicit target occurrences. The inherited all-branch graph
resolver records one successor for INC and beep, two for DECNZ, and one for
each administrative jump. This graph includes both outcomes even if a
particular source invariant would exclude one outcome.

Contract a chain consisting only of administrative jumps until its first
INC, DECNZ or beep. The checker rejects every jump-only cycle, including one
outside the execution from the chosen entry. It checks the entry chain as
well as every outgoing edge. A finite acyclic jump chain has length at most
the number of administrative occurrences in the finite unfolded grammar.
Consequently this contraction cannot hide an infinite silent administrative
execution.

The retained graph records the initial retained occurrence, the ordered list
of all non-jump occurrences and the contracted target of each outgoing edge.
Its labels include the exact register and operation, or the designated beep.
DECNZ success and failure retain their distinct positions and meaning.

## Rewrite acceptance and simulation relation

The measured search considers reassociation of binary pairs, structural
deduplication of identical pairs and removal of a node whose discarded
subtree consists solely of administrative jumps. These proposals do not have
an unconditional local correctness assumption. A proposal is accepted only
after reconstructing the entire retained graph and establishing equality to
the original graph. A syntactically attractive rewrite that changes a jump
target, conditional outcome or entry is rejected. Cyclic control grammars
are rejected as well.

Pair deduplication preserves the fully expanded ordered tree exactly. The
other operations may change the number or locations of administrative
occurrences, so equality of the old uncontracted graph is deliberately not
the claimed relation. Equality of the retained graphs supplies a bijection
by retained occurrence index, with the same primitive label and the same
successor for each conditional outcome.

Relate configurations at corresponding retained occurrences when their
natural-number registers agree. An INC changes the same register by one.
A DECNZ tests the same value, chooses the same branch and, on success,
decrements that value by one. A beep changes no register and emits exactly
one corresponding event. Every intervening administrative chain is finite
and changes no register or event. Thus induction preserves all register
values and the exact ordered beep sequence at successive retained steps.
The finite entry chains give the base case.

This induction is cofinal: each retained step in either graph has a finite
matching execution in the other, and an infinite computation cannot remain
forever inside a removed chain. Each retained physical primitive also
terminates on its valid runtime domain by the inherited scan and unary-bank
proof. Combining the two finite bounds shows that every finite source stage
is still reached after finitely many physical steps. The argument applies
both before and after a possible last event.

## Replay, state cost and limitations

The selected producer never runs the heuristic search. It verifies the
source-specific graph hash and initial dimensions, normalizes identical
pairs, replays five explicit moves, and checks retained-graph equality after
every move. The sequence is two administrative-node deletions and three
pair rotations. The plan records its final dimensions. All resulting raw
physical states, dispatcher depth, register entries, initialization and
event adaptation are generated and counted together.

The heuristic measures pair count plus maximum left depth because these
contribute grammar and dispatcher states. It is not the final state-count
certificate. The literal all-row checker establishes the complete paid
count after generation and exact quotients. Trailing rotations that improved
only height without another paid saving were removed from the frozen plan.

The finite graph checks validate this compiler transformation; they do not
establish NP = coNP or prove the source search theorem. That theorem is a
separate conventional argument in `source/PROOF.md`. The final event theorem
uses the composition in `COMPOSITION.md` and the independent review bindings.
