# Reproducing the theory checkpoint

The exact reviewed source revision, observed results, independent-review scope,
and CI limitations are recorded in [the delivery handoff](../HANDOFF.md).
The latest compact-source evidence is in [the continuation delivery](../CONTINUATION.md).
The original frozen baseline remains separately identified there; continuation
results do not retroactively enlarge its reviewed theorem statements.

## M236 quotient continuation

The checked no-explicit-input literal-M236 guarded acceptance/PA soundness
endpoint and its explicit strategy formulation are in
[PAtoCompactEndToEndProofTranslation](../lean/PASoundness/PAtoCompactEndToEndProofTranslation.lean).
It exposes both finite proof transformations and their separate truth maps;
the proof data are noncomputable, without executable extraction from arbitrary
PA derivability. Two independent private incremental aggregate/audit builds
passed at exact revision `7b551f1722cb62876c04195b6ad1059ac8116e0a` (5,274 jobs
each). Independent end-to-end source review found no substantive mismatch
within scope, relying on imported contracts and separate module reviews, without
its own Lean run or a transitive reproof. See [the observer guide](../OBSERVER-GUIDE.md)
and [M236 continuation](../M236-CONTINUATION.md) for the formal-observer,
historical-prose and record-coding boundaries.

From the repository root, regenerate and compare the literal transcription,
then build the aggregate and audit:

```sh
python3 problems/pa-soundness-lean/code/generate_m236.py --check
cd problems/pa-soundness-lean/lean
lake build PASoundness PASoundness.Audit
cd ../../..
python3 problems/pa-soundness-lean/code/check_m236_game.py
```

The transcription check is external evidence; the separate
`M236TableTextSelected.binding` and `M236TableTextRaw.binding` theorems check
the files embedded by `include_str` against the Lean tables. Use a clean build
after changing an included file. The game check generates 128 finite Lean proofs from
the pinned independent mathematical reference using seed 236. It checks finite
agreement only, not source or physical implementation correctness. The quotient
proof does not implement the producer.

## Running code

From a clean checkout, use the pinned Lean toolchain in
[lean-toolchain](../lean/lean-toolchain) and the committed
[Lake lock](../lean/lake-manifest.json). A normal `elan` installation selects
Lean 4.33.1 automatically inside this project.

```sh
cd problems/pa-soundness-lean/lean
lake exe cache get Mathlib
lake build PASoundness PASoundness.Audit
lake env lean PASoundness/Audit.lean
lake env leanchecker --fresh PASoundness
```

The cache command is optional acceleration for the pinned dependencies. The
subsequent build checks the local source proofs. `Audit.lean` traverses every
project theorem's transitive axioms and fails unless each belongs to
`propext`, `Classical.choice`, or `Quot.sound`; it also prints selected endpoints.
`leanchecker --fresh` replays the imported and project declarations into a fresh
environment with the same Lean kernel. It is an additional replay check, not an
independent implementation of Lean's kernel.
The audit additionally traverses project dependencies of the compact structural
source equivalence and direct normalization semantics, rejecting any use of K
soundness, PA soundness, or truth of HF comprehension in those proofs.

From the repository root:

```sh
python problems/pa-soundness-lean/code/verify_bindings.py
python problems/pa-soundness-lean/code/verify_pa804.py
python problems/pa-soundness-lean/code/review_source.py --axioms
python check.py
python check.py --base 74e2623b5d50d7c32fb1daeaac47b43c4a1a44d0
```

`verify_bindings.py` checks six byte-identical copies, SHA-256/Git blob identity,
the total 926-state/1,852-row binary table, initial configuration, and its two
event rows. It does not execute the producer or infer infinite behavior.
Its optional `--git-object-check` requires the named upstream commits to be
already available locally; it deliberately performs no network or lazy fetch.

`verify_pa804.py` separately verifies the recovered successor's sixteen retained
source/data files, 804-state/1,608-row table and 174/175 exit-event map. It also
checks that its reference record source is byte-identical to PA926. The old
six-entry manifest and its checker are unchanged. The selected build can be
regenerated from the retained closure and checked by the separate recovered
row/graph verifier using the commands in
[bindings/pa804](../bindings/pa804/README.md). These finite checks do not certify
the streamed-field or one-stack semantics, the compiler, or physical progress.

`review_source.py --axioms` compares the pinned Python producer against Lean
evaluation on 192 matrix/environment cases, 64 postfix certificate codes, and
144 axiom-selector cases. The environment cases include repeated-name shadowing.
The script verifies the producer hash before importing it. These 400 exact,
deterministic cases are transcription checks, not a proof of unbounded Python
or machine correspondence. No seed or probabilistic sample is involved. Supply
`--lake /absolute/path/to/lake` if the pinned Lake executable is not on `PATH`.

The repository integrity checker does not prove mathematics or execute research
sources. Run it in a clean checkout without `.lake` build/cache directories;
it rejects symlinks in live research, including possible dependency-cache links.
Do not alter the repository's runner settings or workflows to make a skipped
remote job appear successful.

### Historical interface audit

The exact predecessor is retained as
[OmegaSoundnessInterface.lean.txt](../bindings/predecessor/OmegaSoundnessInterface.lean.txt),
not imported into the project. To reproduce its failed compilation under the
same dependencies, copy it to a temporary `.lean` file and run `lake env lean`
on that file from this project. With the full `Mathlib` cache present, the first
actual error is at line 30: `prefix` is a reserved identifier; downstream uses
also fail. Thus this checkpoint does not count the old interface as checked.
The replacement uses `altPrefix` and proves `failureExact` from quantified duality.

## Reproducibility

The [aggregate module](../lean/PASoundness.lean) imports the mathematical sources.
The finite algebraic PA proof fixtures are in
[CertificateFixtures.lean](../lean/PASoundness/CertificateFixtures.lean).
The compact postfix `program` and `certificate` functions provide a proved
certificate generator for every displayed K derivation. Literal table/source
inputs and origin metadata are in [bindings](../bindings/manifest.json).

The continuation's [CompactNormalization](../lean/PASoundness/CompactNormalization.lean)
defines the total `normalizeCode`, finite derivation transformations and
`certificateFrom` generator in Lean itself. Its strong postfix-tail theorem
preserves every original saved stack. The generated prefix is checked by the
unchanged actual compact recognizer. Both
[normalization fixtures](../lean/PASoundness/CompactNormalizationFixtures.lean)
and [arithmetic interpretation fixtures](../lean/PASoundness/CompactInterpretationFixtures.lean)
are imported by the aggregate build and checked by the kernel. They include
explicit wrong-polarity/rank rejection and capture counterexamples.

The 97 finite AX7/MP proof schemas retained in
[CompactHilbertBasis.lean](../lean/PASoundness/CompactHilbertBasis.lean) have
also been regenerated byte for byte from the hash-pinned recovered
`NumericHilbert238.v` with:

```sh
python problems/pa-soundness-lean/code/generate_compact_hilbert_basis.py \
  --source problems/pa-soundness-lean/bindings/pa238/NumericHilbert238.v.txt \
  --output /tmp/CompactHilbertBasis.lean
cmp /tmp/CompactHilbertBasis.lean \
  problems/pa-soundness-lean/lean/PASoundness/CompactHilbertBasis.lean
```

The translator checks source hash
`fd577e5737cfa733c924bb832d2742ab7ead223c3837a27956c97d0076401223` before
processing it. It does not call Coq or prove anything by itself. The resulting
Lean proof objects are self-contained and all are checked against the exact
K constructors; the historical archive is not needed to build this project.
The exact single reference input, including its original notices, is retained
in [bindings/pa238](../bindings/pa238/README.md) to reproduce the generator too.
The archive's local recovery and unavailable historical objects are recorded
honestly in [source-baselines.md](../source-baselines.md).

The binding audit, differential vectors, proof fixtures, and theorem proofs are
retained; caches, compiled binaries, raw execution logs, and bare PASS reports
are excluded. Warnings about unused simplifier arguments do not introduce
axioms, but unsuccessful builds must never be summarized as kernel verification.
No `native_decide` result is used as a concrete-artifact proof.

### Historical module checkpoints

The following module-by-module notes retain the order and limitations of earlier
checkpoints. Phrases describing a bridge or reachability as open refer to the
individual module or checkpoint being described, not the current literal-M236
end-to-end theorem above. They do not close the separate PA926/PA804 physical
implementation or historical record-coding obligations.

The M236 bootstrap certificate is generated deterministically from the pinned
raw table by [generate_m236_bootstrap.py](generate_m236_bootstrap.py). From the
repository root, `python3 problems/pa-soundness-lean/code/generate_m236_bootstrap.py --check`
checks that the tracked certificate source matches regeneration. The generator
is untrusted: the Lean kernel checks all 77 chunks and their composition in
`PASoundness.M236BootstrapCertificate`. The resulting finite theorem does not
prove the runtime entry or the source simulation. The generated
`PASoundness.M236FirstExit` additionally checks the penultimate configuration
and proves that no earlier transition left the five-state bootstrap subgraph.

`python3 problems/pa-soundness-lean/code/generate_m236_runtime.py --check`
reproduces the packed runtime certificate and fast raw-table lookup from the
pinned raw input. The generator is untrusted: Lean checks the lookup against
all raw-table rows and labels, each of the 333 operation chunks, and their
composition from the certified blank-start bootstrap. The finite result is
`PASoundness.M236.RuntimeGeometry.selected_entry_geometry`; it does not prove
the later source simulation.

`python3 problems/pa-soundness-lean/code/generate_m236_text_binding.py --check`
reproduces the explicit raw and selected byte witnesses and binding modules.
Lean checks their headers and every serialized transition and event label
against the Lean tables, and proves that the `include_str` inputs equal those
witnesses. Rebuild from clean sources after changing an included file.

`M236UnaryShift`, `M236UnaryCodec`, and `M236UnaryNine` check an unbounded
local unary-bank shift against the raw and quotient tables. Their explicit
tape precondition is not yet derived from the selected source execution.
`M236UnaryIncrementNine` additionally matches the local raw state-9-to-35
segment and its mapped quotient segment to the independent increment of any
one of nine registers, preserving the other values and an arbitrary finite
reserve. `M236UnaryReturn` extends the segment to raw state 68 (selected
state 67) when an explicit two-zero left boundary is present, retaining the
full tape and the incremented bank. Source selection, the boundary invariant
and return from state 68 to source control remain open. `M236UnaryCleanup`
continues through the actual state-68/39/40 cleanup to state 1 under an
explicit finite scratch-run precondition, with exact physical tape and time.
This operation erases the first unary bank run; its source-control meaning and
any later reconstruction are not established.


`M236UnaryAnchor` handles an explicit one-cell anchor before the nine independent register
values, restores it after cleanup, and checks return to raw state 79 (selected
state 78) for an explicitly constrained finite control path. The theorem
retains the updated bank and arbitrary reserve in the complete tape, exact
positive time, and the empty event word. Source reachability and the derivation
of its control-path condition from the actual grammar remain open.

The ordinary machine certificate is now instantiated twice for the literal
six-state fixture in [MachineFixture](../lean/PASoundness/MachineFixture.lean)
and [RegisterMachineFixture](../lean/PASoundness/RegisterMachineFixture.lean).
These are quantified finite-block proofs and exact infinite-output theorems,
not bounded execution comparisons. Neither certificate implements the PA
producer. PA926's compiler/runtime/loader and table binding remain open, as
specified in [implementation-refinement.md](../implementation-refinement.md).
The main remaining mathematical/source boundaries are indexed in
[OPEN_PROBLEMS.md](../OPEN_PROBLEMS.md).


`python3 problems/pa-soundness-lean/code/generate_m236_grammar.py --check`
checks that the generated grammar transcription matches the retained pinned
producer metadata. `python3 problems/pa-soundness-lean/code/generate_m236_metadata_binding.py --check`
reproduces the byte and name witnesses. Both generators are untrusted: Lean
checks the entire embedded file against graph-derived serializations and
checks the graph's full rows and events against the literal raw table. This is
not a general JSON parser or source-compiler correctness theorem. Rebuild after
changing the embedded metadata file.


`M236SelectorRoot` checks the prepared named-register increment path through
selection, update, filled-gap cleanup and return to the literal root, with the
full tape and event word. The prepared entry and control-prefix invariants
remain explicit hypotheses; they are not derived from blank execution.


`M236Preparation` checks the actual zero-branch marker and finite gap-fill
rows and composes them with a specified checked grammar path. Its prepared
tape and path hypotheses do not establish reachability from blank execution.

`M236Redispatch` proves the filled-gap return to the grammar root and a
second traversal of a specified named increment path, including complete tape,
exact duration, empty event word, and the 236-state quotient lift. It requires
an explicit control-word encoding, named path, and initial tape relation; it
does not derive those preconditions from blank execution.

`M236CycleCore` checks that every named increment edge preserves its input
bit. `M236Cycle` uses that fact to compose an explicitly given grammar-root
tape through a named path, clean-gap preparation, return, and a second traversal
of that path. The literal quotient segment retains exact time, full tape and
empty event sequence. Root-tape and path reachability remain open.

`M236RootIncrement` composes the root-to-preparation and redispatch segment
with the selected nine-register increment and return, using a proved control
word decomposition. From its explicit root tape and named-path hypotheses it
obtains a positive silent segment on the raw table and 236-state quotient,
with a full final tape and decoding of the updated bank and reserve. Startup
and source-level reachability remain open.

`M236ConcreteIncrement` gives a checked grammar path for every one of the
nine increment entries and realizes its finite zipper as a full two-way tape.
Its concrete family proves a silent finite increment and root return on the
selected quotient from those explicitly constructed tapes. These are prepared
tapes, not an assertion about the blank-start execution.

`M236DecrementSelector` checks all nine named decrement entry states, scans
the arbitrary finite unary selector blocks, and distinguishes the zero and
positive test paths with exact tape, event and quotient-table segments. The
input is an explicit prepared tape. The zero-branch continuation is described
below; the positive-branch continuation is described below; source reachability remains open.

`M236DecrementReturn` continues the zero branch through the literal
left-return states, scanning all preceding finite unary blocks to state 69
and retaining the entire tape. The post-state-69 continuation is described
below; the positive-branch continuation is described below; source reachability remains open.

`M236ZeroCleanup` continues the zero return across an arbitrary finite
scratch run to state 68 with an exact full tape and positive silent quotient
segment. The subsequent prepared zero-branch cleanup is described below;
the positive-branch continuation is described below.

`M236ZeroFullCleanup` completes the prepared zero-branch return to the root,
with an explicit counter/control prefix, and proves the nine-register bank
and reserve remain unchanged. It does not prove that the selected control
branch matches the source program; the positive-branch continuation is below.

`M236DecrementSeek` scans an arbitrary finite positive selected value and
subsequent unary suffix to the backward-shift state, with exact tape and
quotient segment. The backward shift and control return are described below.

`M236DecrementShift` proves the prepared positive branch returns to the
root with the selected register decremented. The exact tape has one additional
zero-valued reserve block at its right edge. Its explicit control-prefix and
prepared-entry assumptions are not derived from blank or source execution.

`M236DecrementPreparation` reuses the same gap preparation on every named
decrement entry and returns through the checked grammar path.
`M236DecrementRoot` composes it with both decrement branches, proves paths
exist for all nine registers, and constructs full two-way prepared tapes with
actual quotient segments. The zero branch preserves the reserve and trailing
blank; the positive branch appends one zero-valued reserve block. None of
these constructed starting configurations is a blank-start reachability proof.

`M236UnifiedDecrement` combines both concrete prepared-tape decrement cases
into a single all-register, all-value theorem, preserving their different
reserve and trailing-cell results explicitly. It does not show these tapes
are reached in the blank-start execution.

`M236BlankFirst` matches the certified blank-start runtime tape to the
four-zero named decrement path and proves the selected literal machine
returns to the grammar root after a positive finite number of additional
silent steps. This establishes one concrete machine segment, not source
compiler correctness, unbounded progress or omega acceptance.

`M236FirstDecode` further identifies the residual control word and exact
zero padding after the first blank-start zero branch. The additional time
and returned head location remain existential; this finite fact does not
establish continued execution or source correspondence.

`M236FirstPullback` uses the checked unique raw preimage of the quotient root
to continue the same run. `M236BlankSecond` proves a second consecutive named
zero-decrement and exact residual control tape, with no output in the entire
blank-start prefix. This remains finite evidence and does not prove source
correspondence or unbounded progress.

`M236Emit` checks paths to marked leaves for both output bits and proves
exact singleton-event segments on the literal raw and quotient tables, with
positive duration and full tapes. These are prepared-path witnesses;
blank-start output reachability and source scheduling remain open.

`M236Control` defines source-independent one- and two-separator decoders of
finite grammar path bits. It proves those decoders terminate on the checked
named paths and that the literal physical increment and both decrement
returns have the decoded control tails. This is not yet a source-program
branch or jump correctness theorem.

`M236PathSuccessor` identifies the physical increment and decrement return
tails with explicit last-zero and second-last-zero path transformations.
It does not yet resolve the resulting path to an instruction in the selected
producer graph or prove the source program's control-flow correspondence.

`M236Sentinel` proves a normal or zero return that reaches the outer
sentinel has an empty residual path, matching the physical root restart.
It does not establish the selected source's occurrence-level control graph.

`M236GrammarSuccessor` checks all 760 adjacent literal grammar leaf pairs.
`M236SkipSuccessor` checks each decodable skipped path and proves that named
zero-decrement returns resolve to a leaf using at most five zero bits. Their
physical compositions follow increment or positive-decrement returns to the
adjacent leaf with an explicit initial gap of at least 3, and zero-decrement
returns to the skipped leaf with a gap of at least 2. These results preserve
the next leaf event and full tape; the source graph and a maintained spacing
invariant are not established.

`M236BlankThird` uses the unique quotient preimage of the root to lift the
existing blank-run result back to the raw table, then follows the third named
zero-decrement (`k.rest`) on that same execution to the root. Its duration and
scratch lengths are existential and the whole output prefix is empty.

`M236Continue` proves the literal continue states scan arbitrary finite zero
runs and one, two, or three markers, preserving the complete tape and exact
silent event word. Its physical compositions reach the grammar root under
explicit counter encoding and root-prefix conditions. Source jump semantics,
and reachability of those conditions remain open. The literal break
transitions are developed below.

`M236EmitReturn` composes a marked output path with a silent one-marker
continue and root return. It retains the exact singleton event and full tape
under explicit path, control-stack, and root-prefix conditions.

`M236ConcreteEmitReturn` discharges those path and control conditions for
each output bit on an explicit prepared grammar-root tape, proving exact
34-step and 36-step marked returns with complete tapes. Blank-run reachability
of these configurations remains open.

`M236ContinueLeaf` composes the checked named `_continue.1`, `.2`, and `.3`
grammar leaves with their literal return scans. It preserves exact silent
events and the full tape, under explicit stack and root-prefix hypotheses.

`M236ContinueCoverage` checks all 760 literal grammar leaves, including 47
`_continue.1`, 157 `_continue.2`, and 23 `_continue.3` occurrences. It
discharges their stack and root-prefix hypotheses for the canonical prepared
root layout. `M236Restart` checks that decoded return paths and a formalized
restart convention resolve to the same literal leaf, including sentinel wrap.
The source program correspondence remains open; the padded physical traversal
is proved below.

`M236Candidate` and `M236RestartAlignment` connect the same reflected
continue candidate to its physical return and to the literal leaf resolved
from the formal restart prefix. The subsequent padded traversal theorem follows that leaf under an explicit
two-zero condition; an invariant maintaining it remains open.

`M236ContinuePadding` kernel-checks that two zero cells suffice for every
named continue destination. `M236ContinueNext` composes the prepared physical
continue return with traversal of that literal destination, retaining the
next leaf’s exact possible event. The two-zero input condition and prepared
root configuration remain explicit; repeated spacing and source simulation
are open.

`M236Break` and `M236BreakLeaf` formalize the literal break scans and
generalized cleanup over arbitrary finite zero gaps, then connect the named
leaves to their returns. `M236BreakCoverage` checks all 42 `_break.1` and 10
`_break.3` occurrences and discharges control-stack conditions for the
canonical prepared root tape. `M236BreakSuccessor`, `M236BreakAlignment`,
and `M236BreakNext` check the formal successor comparison and two-zero bound,
then follow the resolved literal leaf with exact event accounting. The
prepared configuration, two-zero gap, unbounded spacing invariant, and
source-program correspondence remain explicit or open.

`M236EmitCleanup` handles the marked output row that enters cleanup instead
of the continue return. `M236EmitCoverage` checks all 20 fused-output
occurrences: 19 continue-style and one cleanup-style zero output.
`M236EmitSuccessor` checks their formal successor comparison and two-zero
bound, and `M236EmitNext` follows each resolved literal destination. The exact
event word starts with the output bit followed by the next leaf’s optional
event. The prepared tape and two-zero gap remain hypotheses.

`M236AdjacentCoverage` checks that every literal grammar leaf occurs as the
first member of the adjacent-pair list. The increment and positive-decrement
physical next-leaf compositions therefore no longer assume pair membership;
the displayed prepared tape and initial gap bound remain hypotheses.

`M236BlankFourth` continues the actual blank-start run through a fourth
named zero decrement (`k.c`) and computes its control word. `M236BlankFifth`
continues through the following `k.a` increment and proves the exact nine
register values `[0, 0, 0, 0, 0, 0, 1, 0, 0]`, full final tape, and empty
output prefix. Durations, final head, and scratch lengths remain existential.
This finite execution does not establish unbounded producer progress.

`M236BlankSixth` continues that same blank run through the positive `k.a`
decrement, proves the nine registers return to zero, and preserves the extra
zero-valued reserve block required by the implementation. The exact full
tape and empty output prefix are stated; durations and scratch lengths are
existential. This remains finite execution evidence.

`M236BlankFirstEvent` follows the same literal blank-start execution to a
marked `emit.1` row and its root return. Its prior output prefix is empty and
its later prefix is exactly `[true]`, proving the first emitted bit is true.
The complete returned tape is stated; durations, head, and scratch lengths
remain existential. This does not establish later records or omega acceptance.

`M236GapBoundary` checks a concrete prepared zero-gap positive decrement
whose nominal adjacent path needs five zeros. The literal return has only
two zeros before the anchor and subsequently traverses a marked `emit.1`
leaf rather than the adjacent silent `k.rest.decnz` leaf. The full raw and
quotient blocks are proved. This prepared tape is not known to be reachable
from the blank start; the result shows why a gap invariant cannot be omitted.

`M236GapInvariant` proves that every literal grammar leaf has length at most
25, and that the sum of the current leaf length and its zero gap is preserved
by prepared increment and both decrement branches. The theorems give the
full returned tape, the nine-register effect, a positive physical duration,
and the exact silent event word. `M236PayloadInvariant` supplies the general
selected-register bank representation and proves that the certified raw
blank run reaches the canonical initial tape with budget 3,819 and no output.

`M236TransferSpace`, `M236TransferResidual`, and `M236TransferInvariant`
check and apply the corresponding conservation property to the named continue,
break, and fused-output branches. The output branches preserve the literal
one-bit event word. These are local physical segments with explicit named-path,
tape, and budget hypotheses. Their composition into a global reachable-state
invariant and their correspondence to the selected source remain open; the
finite bound 25 is a bound on the fixed machine grammar, not on data or time.

`M236Classification` checks every literal grammar edge and proves that each
finite leaf path ends in one of the supported physical branch forms, including
the correct final read bit for each fused output. It does not compose the
local segments into an infinite physical/source simulation.

`M236RootChain` composes the classified branches into a physical step on a
canonical root tape. It records the named edge, actual register/reserve effect,
exact event word, positive duration and conserved control budget. Starting
from the certified blank-entry configuration, it proves that every finite
number of such steps occurs in the same execution, with the cumulative output
prefix exactly tracked and transported to the selected 236-state quotient.
This proves unbounded grammar-root progress, not source scheduling, record
coverage or omega acceptance.

`M236ControlSuccessor` retains the actual destination rule for each physical
root step: adjacent leaf for increment and positive decrement, decoded skip for
zero decrement, the checked restart or break prefix, and the marked-output
return. Its detailed blank-run chains retain those destination witnesses as
well as register effects, events, and positive durations. These grammar rules
are still to be compared with the selected producer's program semantics.

`M236AdjacentUnique` proves by induction on grammar-unfolding depth that no
path is duplicated, for any grammar graph. Applied to the literal finite
grammar, the adjacent-successor relation has a unique destination. Fixed
restart and break prefix rules and the decoded zero skip likewise have unique
resolved destinations. This does not compare the rebound grammar to the
producer occurrence graph.

`M236OccurrenceGraphData`, `M236OccurrenceGraphCheck`, and
`M236OccurrenceGraphSound` retain an untrusted producer-derived occurrence
graph and compare every row with the literal grammar; `M236OccurrenceGraphCount`
checks the retained graph's 1,036 edges. The checked conditions
cover operation names, valid destination indices, both decrement outcomes,
resolved jumps, and output returns. The checker-soundness theorem gives those
conditions as Lean propositions. The conventional Python extraction is not a
proof of producer-source semantics or an exact JSON-to-Lean serialization proof;
see the binding README for the pinned input and reproduction commands.

`M236OccurrenceGraphAdapters` connects checked graph rows to the physical
control-successor rules: the normal adjacent edge, zero-decrement edge, each
continue and break level, and both output polarities. The lemmas retain the
explicit occurrence index and physical named-path hypotheses; source-program
semantics and an iterated graph simulation are not yet established.

`M236OccurrenceGraphIndexed` maps any named physical control successor to a
retained graph row and edge, preserving its operation label and next path.
`M236OccurrenceGraphExecution` annotates each segment of the existing
blank-run chain this way and carries its exact event prefix to the selected
236-state machine. That annotation predicate alone does not assert that successive graph
indices form a single indexed walk; the following module supplies such a walk.
The producer-source semantics remain open.

`M236OccurrenceGraphWalk` strengthens the annotation into a continuous indexed
walk: the target index of each physical step is the index of the next step.
For every finite length, the literal blank-start execution realizes that walk
with positive physical durations, the exact register and reserve effects,
canonical full tapes at every boundary, the correct zero/nonzero edge, and
the exact cumulative event prefix. The checked graph witness is not yet proved
to be the selected producer program or its mathematical record semantics.

`M236OccurrenceGraphProjection` defines a tape-independent relation on the
retained graph index, nine-register bank and reserve, and proves that each
physical graph step projects to it. For every finite length, the actual M236
blank run realizes a corresponding graph walk from the explicitly specified
initial graph state with the same emitted prefix. The reverse simulation,
producer-program meaning, record coverage and PA endpoint remain open.

`PeanoMultiplication` constructs genuine object-level PA derivations of
`∀x, 0 × x = 0` and its instance at an arbitrary arithmetic term, using the
explicit multiplication and addition axioms, equality substitution, and the
full PA induction schema. It is reusable arithmetic groundwork; it does not
prove the translated bit refutation, finite comprehension, or PA/K proof
transport.

`FOLFreshEquality` constructs a fresh free variable for any finite term and
uses the calculus's equality-substitution axiom to derive symmetry and
transitivity for arbitrary terms in any first-order language. It also provides
rules for ordinary derivations and finite proof contexts. The proofs are
syntactic and do not invoke a model-soundness theorem.

`PeanoMulOne` uses that fresh-variable equality interface to derive in the
actual PA calculus that `t × 1 = t` for every arithmetic term `t`. This is an
object-level proof, not a standard-model evaluation.

`PeanoAddition` derives successor congruence and `t + 1 = S t` for arbitrary
terms. `PeanoOneMul` derives addition congruence and the genuine PA theorem
`1 × t = t`, including a universally quantified version obtained by induction.
These are object-level proofs and do not settle the coding or transport bridge.

`M236CoherentExecution` uses the proved positive graph segments to construct a
single coherent sequence of boundaries on the selected blank-start run. Its
elapsed times strictly increase and its accumulated outputs equal the literal
machine's output prefixes; it does not establish producer or observer meaning.

`generate_m236_graph_text.py --check` reproduces the untrusted chunk witnesses
for `M236OccurrenceGraphText`. Lean checks their rows and the exact retained
occurrence-graph file bytes; it does not verify the producer's Python execution.

`M236OccurrenceGraphEvents` derives exact silent/zero/one output from each
checked occurrence-graph operation and transfers it to the corresponding
segment of the selected blank-start run. It does not prove record coverage.

`M236ListSchedule` proves an alternative experimental self-delimiting coordinate
list and Cantor stage encoding invertible for arbitrary nonempty finite lists.
This is not the selected M236 producer schedule.

`M236ListScheduleObserver` proves address coverage in an alternative one-stage-
per-address order. `M236ListSource` proves its guarded acceptance agrees with
the repeated-address abstract source, and `M236ListSourceSelected` instantiates
this for the selected value function. This alternate order is not the selected
producer's trace and is not used as the physical-source refinement premise.

`M236OccurrenceGraphDeterminism` identifies every relational graph step with
an explicit deterministic row interpreter. `M236OccurrenceGraphConverse`
lifts every finite witness walk from the initial graph state to positive-time
segments of the literal selected blank-start run, with exact output. This does
not prove that the producer constructs or correctly uses the graph.

`M236GraphOutputRefinement` proves complete ordered-output equivalence between
the deterministic retained graph interpreter and the literal selected machine.
`M236FrameProgressTransfer` preserves the frame-progress guard for equal-output
singleton-bit systems, and `M236GraphFullObserver` obtains the full fixed
observer equivalence. The graph-to-source and PA proof bridges remain open.

`M236SourceGraphBridge` states the exact conditional composition from the
literal machine to compact and genuine PA soundness. Its source-to-graph
`WordRefinement` and compact-to-PA equivalence are explicit, undischarged
premises; this module does not establish the requested unconditional endpoint.

`M236GraphCopy` proves the first scheduler copy routine for arbitrary natural
register values, including exact graph time, silent output, restored scratch,
other-register preservation and reserve growth. It lifts the result to any
reachable selected-machine boundary and proves the initial zero-valued case.
The rest of the source scheduler and full refinement remain open.

`M236GraphMove` verifies the unpairing loop's `c`-to-`a` transfer for arbitrary
values and its lift at reachable selected-machine boundaries. The modules below
extend this to the full unpairing routine; arbitrary entry reachability remains open.


`M236UnpairDiagonal` proves the arbitrary-input diagonal/Cantor inverse identity.
`M236GraphUnpair` verifies the selected graph's first unpairing and its physical
lifts at reachable boundaries. `M236GraphEmitUnary` proves exact unary output
with restored scratch for arbitrary input. `M236RankHeader` composes copy,
unpairing and rank output for the actual repeated-address schedule; the lift
assumes a reachable clean scheduler entry, and the zero-stage blank-start case
proves the finite prefix `[true, false]`. It does not prove all-stage coverage,
complete records, the source refinement, or the PA/K bridge.


`M236GraphRankCount` verifies the rank-to-counter transfer, its exact silent
duration and physical lift at reachable boundaries. It composes unary output
with the transfer to the next unpairing entry; the rest of the record and
all-stage reachability remain open.


`M236GenericUnpair` proves one parameterized unpairing schema and checks its
occurrences at graph entries 7, 30, 57 and 84. It composes rank emission and
the counter transfer with the second unpairing, lifts the composition at
reachable physical boundaries, and proves a finite blank-start second-unpair
exit. It does not establish all-stage reachability or complete records.

`M236GenericEmitUnary` checks one unary-emitter schema at graph entries 19,
41, 68 and 95. It proves exact output, restored zero scratch, reserve growth,
and a physical lift at a reachable entry; it also composes the schema with
the shared unpairing routine. `M236SecondField` composes the rank emission,
counter transfer, second unpairing and next unary field, and lifts this block
at a reachable physical boundary. These prepared-entry results do not prove
the source meaning of the second component, repeated stage reachability,
complete records, or the PA equivalence.

`M236FieldTransfer` checks the post-emission transfers at entries 49 and 76.
For arbitrary values, the transfer clears `a`, adds its old value to the
destination (`top` or `b`), preserves all other registers, appends that many
reserve zeros and emits nothing in exactly `3*n+1` graph steps. It composes
the emitter and transfer, and composes the rank and second field through the
`top` transfer to entry 52. Physical lifts require a reached prepared entry.
The subsequent control flow, repeated scheduling, source semantics and PA
equivalence remain open.

`M236FieldBranch` checks the positive-counter branch from entry 52 to 57,
composes it with the next Cantor unpairing, and then emits its first component
and transfers it into `b` at entry 79. The exact three-field graph word, full
end state and a physical lift are proved under explicit initial work-register,
positive-counter and reachable-entry conditions. The zero-counter branch,
later fields, source interpretation, repeated stage reachability and PA
equivalence remain open.

`M236CounterDispatch` checks both the positive and zero-counter branches at
entries 52 and 79. A zero counter silently drains `top` and reaches entry 724,
with exact time and reserve growth. It composes that case with the three-field
path and lifts it to a reachable physical boundary. The actual blank-start
run reaches entry 724 with prefix `[true, false, false, false]`. This finite
prefix is not a proof of a complete record, repeated scheduling, source
correctness or omega-acceptance.

`M236FirstFrame` proves the final zero-result cleanup for an explicitly zeroed
work bank. On the actual blank-start run it proves the exact unary frame for
address `(1, 0, [0])` and bit `false`, followed by a graph boundary with stage
1 and all other registers zero. The finite reserve is preserved by the final
eight graph steps and retained existentially at the boundary. This does not
prove the selected value function, later records, unbounded progress in source
stages or the PA equivalence.

`M236SecondStage` composes the actual first-frame boundary with the scheduler
rank-field block for stage 1. It proves the same blank-start run appends the
rank-two unary header and reaches the exact graph boundary for subsequent fields.
The remaining second-frame fields and value, repeated stages, source semantics
and PA equivalence remain open.

`M236StageThreeFields` composes the scheduler copy, first unpairing and the
first three unary fields for any natural stage from an explicitly clean
prepared entry. It proves that the emitted rank, certificate and first
coordinate match `Schedule.scheduledAddress`, with exact graph endpoint and
reserve. Its physical lift assumes that entry is reached. Later coordinates,
value computation, repeated stages and the PA equivalence remain open.

`M236StageFourFields` continues through the positive counter branch and the
next unpairing and emitter. At a clean entry for a stage of rank at least two,
it proves the ordered scheduled rank, certificate and first two coordinates,
with an exact graph endpoint and reachable-entry physical lift. A specialization
follows the actual blank-start run through those fields at stage 1. The value
bit, further coordinates, repeated stages and PA equivalence remain open.

`M236CoordinateBudget` proves the successful coordinate-budget scan at
entries 103–118: when the coordinate is at most the counter, it restores the
counter and `a`, adds the coordinate to `env`, clears `c`, and reaches entry
119 silently in exactly `10*n+2` graph steps, appending three `n`-zero reserve
blocks. It composes the scan with the four-field block, gives a reachable-entry
physical lift, and specializes it to the actual stage-one run. The exceeding-
budget case is addressed below; subsequent computation, repeated stages and PA
equivalence remain open.

`M236CoordinateOverflow` proves the complementary exceeding-budget path. It
restores the consumed counter, drains `top`, retains the unconsumed `a` remainder
and reaches entry 724 silently with exact graph time and reserve effects. The
success and overflow theorems yield an exhaustive dispatch to entry 119 or 724
after four scheduled fields, with a reachable-entry physical lift. The later
meaning of these branches, full records, repeated stages and PA equivalence
remain open.

`M236ResidualCoordinates` proves the loop at entry 726 emits an arbitrary
finite list of decoded coordinates in order, leaves the residual packed tail,
clears its work registers and reaches entry 749 after positive finite progress.
The packed-list version gives the exact encoded list and arbitrary tail, and a
physical lift assumes the displayed prepared entry is reached. Connecting this
entry to every relevant prior branch, final record semantics, repeated stages and
PA equivalence remain open.

`M236ResidualEntry` proves that graph entries 724–725 silently drain `a` in
`2*n+1` steps and then compose with the remaining-coordinate loop. For a clean
prepared scheduler entry with rank `count+2` and an overflowing second
coordinate, the composed graph block emits the entire scheduled address word
and reaches entry 749 in positive time. Its physical lift assumes that the
selected execution reaches the stated entry. The final value bit, cleanup,
all-stage reachability and source refinement are not established by this block.

`M236FinalCleanup` proves that prepared graph entry 749 drains `rest`, `env`
and `b`, emits `top` one-bits followed by zero, and increments the stage with
exact duration and reserve growth. If `top` and the remaining work registers
are zero, it emits a single false bit and reaches a clean next-stage bank. It
also composes this case with residual-coordinate output as a graph block. A
separate physical lift covers the final cleanup when its specified entry 749
is reached. This module alone does not connect the overflow path to those
cleanup hypotheses or prove all-stage reachability.

`M236OverflowFrame` composes the overflow path with the final cleanup. Given a
prepared clean scheduler entry, a positive rank `count+2` and an overflowing
second coordinate, it emits exactly the scheduled frame with its selected
false value and returns to a clean `stage+1` entry in positive time. Its
physical lift assumes the displayed entry is reached on the selected run.
That module alone does not cover the bounded-coordinate branch or all stages.

`M236HalfPass` verifies one silent divide-by-two pass through graph rows
119–132 for arbitrary natural input, with exact time and reserve growth. It
composes the pass with a successful positive coordinate-budget exit and gives
a physical lift under an explicitly reached-entry hypothesis. On top of that
pass, `M236RepeatedShift` proves arbitrary repeated shifts and parity
extraction produce the exact `Nat.testBit` value, and composes with the
successful budget block. Its physical lift also assumes a reached entry. The
later evaluator and full refinement are established by subsequent modules.

`M236InitialEnvironment` verifies the separate prepared graph routine at
entries 145–161: it silently initializes `env` to `Cantor.pair y 0`, with
positive finite duration, preserved other registers and finite reserve growth.
Its physical lift assumes the stated entry is reached. This module alone does
not connect to the preceding bit extraction or the later evaluator.

`M236BoundedInitialization` connects the successful budget branch, indexed
bit extraction and environment initialization through entry 161. Its
scheduler-level graph block retains the exact four-field word and destination
bank. Physical lifts assume the specified intermediate entries are reached;
this module alone does not establish the later evaluator or all-stage execution.

`M236BoundedTimeout` proves both bit polarities with zero remaining counter
reach cleanup, emit a false result and return to a clean next-stage bank. It
combines this bounded case with overflow to cover every prepared rank-two
scheduler entry. On the actual selected blank-start run it proves two complete
frames, a clean stage-two boundary, and equality with the abstract source's
two-frame prefix. This finite equality does not establish all-stage source
refinement or omega acceptance.

`M236RankOneFrame` proves that any clean prepared rank-one scheduler entry
emits its complete selected-source frame with false value and returns to a
clean next-stage bank. Its physical lift requires a reached entry; a separate
prepared-stage fixture identifies stage two's address and payoff. It does not
itself establish blank-start reachability of that fixture.

`M236ThirdSourceFrame` composes that case with the actual blank-start
two-frame result, proving equality with the abstract source through three
frames and a clean stage-three boundary. `M236CoveredStages` composes finite
intervals of the proved rank-one, rank-two, overflow and bounded non-atomic
timeout cases, with explicit coverage and initial-boundary hypotheses; it
checks coverage of the first three stages. Its narrow coverage predicate is
not universal; the subsequent refinement uses an exhaustive case split.

`M236CoveredRefinement` proves that positive, exact clean-stage frame blocks
for every stage and finite reserve yield cofinal ordered source-to-graph and
source-to-machine refinements. Its earlier narrow `CoveredStage` predicate is
provably not universal: stage 12 is outside it, so that specialization remains
vacuous. `M236SchedulerRefinement` supplies the stronger frame-block premise
using the complete bounded case, rank one and overflow, and proves equivalence
of the selected physical observer with compact-calculus soundness. Genuine PA
proof transport is supplied by the separate end-to-end module linked above.

`M236PositiveCoordinate` verifies a reusable positive-count coordinate
dispatch at both checked occurrences and composes the bit-zero alignment and
bit-one paths from entry 161 through their next graph entries. It records the
unary output and full bank effects, with physical lifts conditional on reached
entries, and connects both cases to the preceding bounded initialization.
This module alone does not establish signed-evaluator or producer-to-graph correctness.

`M236PairEnvironment` verifies a shared prepared environment-pairing schema
at four checked graph entries. With a clean accumulator it computes
`Cantor.pair newValue oldEnvironment`, clears the input and accumulator
registers, preserves all other bank values and emits no bits; its physical lift
requires a reached entry. Later modules connect it to the signed evaluator.

`M236FormulaScan` verifies a register-specific Cantor diagonal scan and its
zero and positive tag branches at three graph occurrences, preserving the
other registers and tracking finite silent progress and reserve growth. It
composes the bit-one positive-count coordinate path with the scan and each
branch. Its physical scan lift assumes the prepared entry is reached; later
evaluator semantics and source correspondence are addressed by later modules.

`M236ChildSelect` verifies both move branches of the shared child selector,
environment pairing and continuation. At a prepared row-393 entry with
nonzero formula tag and zero `top`, it proves a silent graph block that puts
the abstract `M236Game.child` into `top` and pairs `move - 1` (natural
subtraction) with the prior environment. Its physical lift assumes that entry
is reached. Full evaluator recursion and the atomic case are addressed by later
modules.

`M236SignedNonatomic` extends that local child/environment update to all three
checked signed occurrences and composes each with a positive-count coordinate
emission. It identifies the corresponding non-atomic abstract evaluator
clause and supplies physical lifts at reached entries. The formal relation
between continuation states and evaluator polarity, the atomic case, recursive
walk invariant and producer-to-graph correspondence remain open in that module.
`M236SignedWalk` proves a finite induction over consecutive non-atomic moves,
including phase alternation, ordered unary output, counter and environment
updates, and the exact-budget timeout with false result and clean return.
Its physical lifts require reached prepared entries. Atomic evaluation and
all-stage refinement are established by later modules.

`M236AlignedTimeout` composes clean scheduler initialization, both
polarity-sensitive alignment paths and the finite non-atomic walk. Under the
explicit bounded-coordinate and non-atomic timeout hypotheses it proves the
complete selected-source frame and clean next-stage return; its physical lift
assumes the clean entry is reached. Atomic paths and all-stage refinement are
established by later modules.

`M236EnvironmentLookup` checks the shared prepared lookup schema at six graph
entries. For arbitrary encoded environment and index it computes the abstract
`M236Game.lookup`, including default zero, and tracks the unused encoded tail,
other registers, silence and finite reserve growth. Its physical lift assumes
the specified entry is reached. Later modules complete the atomic evaluator.

`M236AtomFirstLookup` composes two prepared environment lookups at three graph
occurrences, placing the atom's bit index and container into the appropriate
registers and identifying their mathematical meaning with `encodedAtom`. Its
physical lift requires a reached entry. Payload decoding and execution of the
subsequent bit test are outside that module.
`M236AtomicBit` composes both prepared lookups with the checked graph bit scan
and sign handling at all three atom occurrences, reaching entry 724 with the
correct `encodedAtom` payoff or its complement in `top`. Physical lifts assume
the stated entries are reached. Later modules prepare the payload and connect
the evaluator to the source.

`M236SignedAtom` composes each prepared tag-zero scan with paid-move cleanup,
payload decoding, atomic lookups, bit and sign handling. It also emits the
remaining coordinates and Boolean payoff and returns to a clean next-stage
bank. Its physical lift assumes the displayed entry is reached. The upstream
evaluator walk and all-stage source correspondence remain separate.

`M236SignedAtomWalk` composes a finite non-atomic prefix with the first paid
atomic move and remaining fields, including both initial alignment polarities.
Under explicit bit, budget, environment and packed-tail hypotheses, it
identifies the emitted payoff with `selectedValue` and returns to a clean
next-stage graph entry. It does not establish reachability or the full
scheduler-frame composition.

`M236SchedulerAtom` composes the first-atom case with the clean scheduler and
proves the finite first-atom/timeout split. It establishes a complete selected
frame and clean next-stage return for every successful-budget scheduler entry,
and explicitly covers stage 12. `M236SchedulerRefinement` combines this case
with rank-one and overflow cases into the all-stage refinement.

`M236ObserverFrontDoor` expands the guarded trace-acceptance definition into
explicit completeness, frame-progress and per-game strategy conditions, and
checks rejection controls for missing records, conflicting records, malformed
rank and a permanently unfinished field. It also checks that distinct games can
require distinct witnesses. See [the observer guide](../OBSERVER-GUIDE.md) for
the proof path and the remaining formal binding to the historical specification.

`PeanoOrderIrreflexive` constructs an object-level PA derivation of the
irreflexivity of the exact strict-order formula used in the compact
interpretation. It reduces translated bottom to the explicit PA derivation
that the same-variable bit predicate implies strict self-order. The later
growth proof discharges the bit-position route; parameterized comprehension
remains open.
`PeanoBitPositionReduction` eliminates the three existential witnesses in the
exact bit formula and reduces that derivation to explicit object-level power
growth and quotient/remainder order implications. Both implications remain
unproved in that module; this is a conditional proof transformation.
`PeanoAdditionAssociative` derives addition laws and discharges the exact
quotient/remainder order implication inside PA. It leaves power growth as an
explicit premise, discharged by the later `PeanoPowerGrowth` module.
`PeanoPowerGrowthStep` derives the base `0 < 1` and arithmetic doubling
step `x < p → S x < p+p` in PA. `PeanoBetaBound` derives the bound on a
literal beta-row remainder and its power-trace base-row instance in PA.
Neither result proves the beta-trace induction or the power-growth premise.
`PeanoAdditionCancellation` proves PA left-addition cancellation and equality
of remainders when the quotient terms are equal. It does not prove quotient
equality or uniqueness for arbitrary beta rows.
`PeanoOrderAsymmetry` derives strict-order asymmetry for arbitrary arithmetic
terms inside PA.
`PeanoOrderSuccessor` derives both directions of `a<b` iff `S a<S b` for
arbitrary terms in PA. `PeanoOrderTotality` uses nested PA inductions to derive
`a=b ∨ a<b ∨ b<a` for arbitrary terms; this does not yet prove beta uniqueness.
`PeanoOrderTransitive` derives strict-order transitivity and excludes a
three-edge strict-order cycle inside PA.
`PeanoMultiplyQuotientStep` derives the adjacent-quotient inequality
`r<m → q*m+r < (S q)*m` inside PA for arbitrary terms.
`PeanoQuotientGap` extends this to arbitrary quotient gaps and derives
uniqueness of quotient and remainder for two explicit bounded rows in PA.
`PeanoBetaUnique` eliminates the existential quotient witnesses and derives
uniqueness of the actual beta output inside PA for arbitrary terms. The
positive-index power-trace endpoint and induction proof remains open.
`PeanoPowerZero` derives the literal zero-index endpoint `pow2 0 p → p=1`
and its growth consequence `pow2 0 p → 0<p` inside PA.
`PeanoPowerTransition` extracts, inside PA, the actual predecessor beta row
whose value doubles to the endpoint of a successor-index power trace, while
retaining the original bounded trace and code witnesses. It does not itself
restrict that trace to the predecessor index or prove the full growth induction.
`PeanoPowerPredecessor` carries out that trace restriction inside PA and
repackages the witnesses to derive `pow2 (S n) p → ∃r (pow2 n r ∧ p=r+r)`.
`PeanoPowerGrowth` carries out the growth induction in PA, discharges the
translated-bottom obligation and specializes the compact-to-PA proof
transformation to the remaining parameterized-comprehension premise.
`PeanoAX8Comprehension` later supplies the full guarded family, and
`PeanoCompactProofToPAClosed` discharges the premise to construct the proof
translation with separate truth-preservation interfaces. The separate guarded
reverse proof transport is linked in the current endpoint above.
`PeanoEmptyBitSet` proves inside PA that zero has no bits and derives the
zero-code filtering body when the predicate is everywhere false. This is a
restricted base case, not the general comprehension family.
`PeanoPowerSingleton` proves in PA that a literal power trace `pow2 n p`
sets bit `n` of `p`. It does not establish power-trace existence, absence of
other bits, insertion or general comprehension.
`PeanoPowerExistenceBase` constructs the literal `pow2 0 1` derivation in PA
from explicit beta-code witnesses. General power-trace existence still requires
the trace-extension step.
`PeanoPowerOneCutoff` proves the one-index cutoff and constructs the two
literal beta rows for one concrete doubling step in PA. It does not yet
package them into a full trace or establish general trace extension.
`PeanoBetaCodeExtension` and `PeanoBetaProductIncrement` derive preservation
of one row under a modulus multiple and of two rows under the product of their
moduli. `PeanoBetaInverseAppend` constructs a new row from an explicit inverse
certificate and bound while preserving an old row under an explicit
divisibility equation. `PeanoBetaPairInverse` supplies an explicit fixed-pair
inverse for a positive product-form parameter, and `PeanoBetaPairUpdate` uses it
to preserve one row and install a bounded second row. Bounded-family trace
extension remains open. `PeanoCommonMultiple` and `PeanoCommonPositive`
construct bounded common parameters in PA; `PeanoBetaUniformPairs` supplies
per-pair beta-modulus inverse witnesses for one such parameter.
`PeanoBetaCRTEndpoint` constructs a single code for bounded rows in PA under
explicit row-totality and pairwise-inverse conditions for the same parameter;
supplying those conditions for a power trace remains open.
`PeanoDivisionTotality` derives quotient and remainder existence in
PA for positive moduli; `PeanoBetaExistence` uses it to derive an output for one
literal beta row. `PeanoPolynomialQuotient` and `PeanoPolynomialContext` let
polynomial identities yield PA derivability proofs, with the latter retaining a
fixed context; they are not executable proof-tree extractors.

`M236FirstRecord` defines first eligible timed receipts and a false default.
On complete traces its value agrees with the unique receipt at every legal
address and restates the existing guarded acceptance in those terms. The
comparison for cumulative word traces assumes no error; the separate historical
guard transcription and its review are described below.

`M236FrameProgressBinding` proves that complete coverage of the rank-one
address family forces cofinal clean boundaries for physical singleton-bit
systems. Thus the separate frame-progress guard follows from completeness
for the literal machine. Malformed output can satisfy frame progress by itself.
`M236FrameSegmentation` proves an exact finite decoder segmentation invariant
and, for error-free physical bit streams, the equivalence between progress and
each emitted bit eventually belonging to a completed legal frame.
`M236HistoricalGuard` defines four manuscript-style guard clauses on raw
frame occurrences and proves their equivalence to the observer guard for
physical bit streams, as well as equivalence of the corresponding first-record
acceptance predicates. Independent review of the transcription against the
historical manuscript and its precise scope are recorded in the continuation.
