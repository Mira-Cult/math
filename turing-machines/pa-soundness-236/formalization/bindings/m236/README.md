# M236 literal intake

The target is the 236-state quotient, not the PA804 reference. These inputs
are copied byte-for-byte from PR54 delivery `60c6f2c22ddd50d3ba40e2ca94a4a63a87e74a0c`,
producer `bad500e2d22c3f8b7c6420f5c5b1a504a6a57b30`, under
`problems/pa-full-soundness/experiments/pa266-architecture-20261031/artifacts/fused236/boot/`.

| File | SHA-256 |
| --- | --- |
| [machine.tm](machine.tm) | `bcf4a1fd22e9959a4145688d05ec20591d97967050ad1a16beeb22a187edaedc` |
| [raw.tm](raw.tm) | `e73b3c7fbcbbc4614e4ee33a6e33cacfb3b8e2dc32822591db2afdfedf01a9e8` |
| [quotient.json](quotient.json) | `23491bc2faecf603190bab3ebbae89ab7fe7bf019f1b075ae1499183df4eae01` |
| [semantic_reference.py](semantic_reference.py) | `ba4786c9363b66db0a9528328b9ac05b2f0ab95f68e0bd7d0db61554d5dfafa7` |
| [producer-metadata.json](producer-metadata.json) | `cfd15b5d5eb62357ee4a9808d6e3cf044eab9ff2fdcbc1e8f0880046c5d4752e` |

The header fixes initial state 0, head 0 and a blank zero tape. A row gives
state, read, write, direction, next state and optional emitted bit. The four
labelled quotient rows are `(134,0)→1`, `(136,0)→1`, `(137,1)→0` and
`(146,0)→0`; unlabelled rows are silent. Labels describe transitions, not
state occupancy. The raw table contains 237 states; the quotient contains 236.
The companion initializer is not used. The independent finite mathematical
reference is copied from the producer's `semantics/semantic_reference.py`;
it is a regression input, not an implementation certificate.

[The generator](../../code/generate_m236.py) validates the pinned bytes and
transcribes the rows and quotient map into Lean literals. Lean also checks
that explicit byte witnesses are exactly the serialization of both Lean
tables, including all row event labels; see
[M236TableRowsConnect](../../lean/PASoundness/M236TableRowsConnect.lean).
[M236TableTextSelected](../../lean/PASoundness/M236TableTextSelected.lean)
and [M236TableTextRaw](../../lean/PASoundness/M236TableTextRaw.lean) prove
that the corresponding files embedded by Lean's `include_str` have exactly
those bytes. The ASCII conversion is proved in Lean; neither the Python
generator nor a hash comparison is used as the equality proof. A clean rebuild
is required after changing an included file: `include_str` embeds its contents
at elaboration, and Lake may not track changes to that external input.
The kernel sees the resulting literal data and checks the mathematical
statements in [M236Quotient](../../lean/PASoundness/M236Quotient.lean).
No statement here connects the raw table to the selected source program.


The producer metadata is copied from the [pinned raw boot artifact](https://github.com/Mira-Cult/math-wip/blob/60c6f2c22ddd50d3ba40e2ca94a4a63a87e74a0c/problems/pa-full-soundness/experiments/pa266-architecture-20261031/artifacts/fused236/boot/raw/metadata.json).
The untrusted `generate_m236_grammar.py` transcribes its 158-node grammar and
state names; `generate_m236_metadata_binding.py` supplies byte witnesses.
Lean proves the exact embedded file bytes equal a concatenation containing
all graph-derived grammar, grammar-name and state-name rows, plus the root
and dispatcher fields. It checks their object boundaries and complete index
orderings, and checks the graph's rows, events and terminal-name resolutions.
The other exact file bytes remain explicit witness spans. This is a concrete
serialization equality, not a correctness theorem for a general JSON parser;
it also does not establish that the producer source program compiles to this
graph. Rebuild after changing the file: `include_str` embeds its contents and
Lake may not track that external input. Neither generator is trusted.

[occurrence-graph.json](occurrence-graph.json) is a finite graph witness
reconstructed from the selected producer at `bad500e2d22c3f8b7c6420f5c5b1a504a6a57b30`.
Its SHA-256, including the final newline, is
`dbad7675ad75b28ff70f26387f0cb6cbeabe5dea586d681eefa47c11c422ae93`.
The conventional reconstruction compares the original and rebound occurrence
graphs; it is not a proof that the Python producer realizes
the mathematical record source. To reproduce it from a repository that has
the pinned commit, in an isolated temporary directory:

```sh
mkdir -p "$TMPDIR/m236-producer"
git archive bad500e2d22c3f8b7c6420f5c5b1a504a6a57b30 -- \
  problems/pa-full-soundness/experiments/pa266-architecture-20261031 \
  problems/pa-full-soundness/experiments/pa576-architecture-20261031 \
  problems/pa-full-soundness/experiments/pa804-continuation \
  problems/pa-full-soundness/experiments/pa800-grammar | tar -x -C "$TMPDIR/m236-producer"
PYTHONDONTWRITEBYTECODE=1 python3 problems/pa-soundness-lean/code/reproduce_m236_occurrence_graph.py \
  --producer-root "$TMPDIR/m236-producer" --check
python3 problems/pa-soundness-lean/code/generate_m236_occurrence_graph.py --check
```

The generator transcribes this untrusted witness as Lean literals. Lean checks
the literal rows against the grammar with a proved checker-soundness theorem;
the relation between the Python execution and these literals is reproducibility
evidence, not a kernel-checked Python semantics or exact JSON serialization
proof. The Lean literals themselves are the certificate input.
