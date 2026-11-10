# Construction and proof guide

This is an explanatory proof map for the exact [machine](machine.tm) and
[observer](OBSERVER.md), with complete proof terms in the accompanying Lean
source. The elementary scheduling/game arguments are explained below; the
large physical simulation and proof translations are linked at their precise
interfaces rather than replaced by an assertion that a compiler is correct.

## 1. What the machine actually does

M236 enumerates **addresses**, computes a finite Boolean game value at each
address, and prints a unary frame. It does not enumerate PA proofs on its tape
and does not run a noncomputable truth evaluator. The infinite observer supplies
the alternating quantifiers that give the output its mathematical strength.

The original construction is a grammar-based register-machine program compiled
to a binary tape machine. It includes its own blank-tape initializer. A
237-state raw table is reduced to the selected 236-state table by an
output-preserving quotient. The original builder, plans and source dependencies
are preserved in [producer](producer/README.md); the exact literal tables and
quotient map are also frozen under
[formalization/bindings/m236](formalization/bindings/m236/).

### The exact repeated-address schedule

Use this orientation of Cantor pairing:

```math
\langle a,b\rangle=\frac{(a+b)(a+b+1)}2+b.
```

At stage `s=0,1,2,…`, unpair `s` into `(r,z)`, unpair `z` into `(p,w)`,
and set `n=r+1`. Unpair `w` repeatedly `n` times, taking each first coordinate
as the next move and continuing with the second. Discard the final residual
tail. This yields the address `(n,p,[x₁,…,xₙ])`.

For a legal address `a` and any residual tail `q`, recursively pair its moves
onto `q`, then form

```math
s_q=\langle n-1,\langle p,\mathrm{pack}(xs,q)\rangle\rangle.
```

Decoding `s_q` returns exactly `a`, and `s_q≥q`. Thus every legal address
occurs beyond every bound, not merely once. The repetition is deliberate and
cannot be replaced by the experimental self-delimiting-list order when
reasoning about this exact table. These equalities and fairness are proved in
[Schedule](formalization/lean/PASoundness/Schedule.lean).

### H-formula codes and their finite evaluation

The selected game syntax is unusually small. Unpair a natural code `f` into
`(tag,payload)`.

- If `tag=0`, unpair `payload` into `(j,g)`. The atom asks whether the natural
  number at environment position `j` is a binary-set member of the number at
  position `j+g+1`: bit `env[j]` of `env[j+g+1]` is one. Missing environment
  positions have value zero.
- Otherwise put `a=tag−1`, `b=payload`. The semantic H-constructor is

```math
T(f,E)=\neg T(a,0::E)\ \lor\ \exists x\,\neg T(b,x::E).
```

Both children are smaller than `f`, so this defines a finite syntax. The
membership atoms have strictly ordered *positions*, not bounded values.
Capture-safe syntax translations later recover the richer compact language.

A finite path carries an environment and a sign. Before inspecting even an
atom, it must consume one available move slot. At an H-node, move `0` selects
the left child and binds zero; move `m+1` selects the right child and binds
`m`. The sign flips. At an atom, it checks the atom or its negation according
to that sign. If the slots run out first, the answer is **optimistically true**,
for either sign. Unused moves after a resolved atom do not change its value.

A positive signed game starts with an existential move. A negative signed game
starts with a universal move; `aligned` adds an ignored initial existential
slot so both fit the observer's fixed existential-leading convention.

### The exact emitted Boolean

For rank `n=1`, emit `b=0`. For `n=r+2`, write the moves as
`[C,y] ++ rest`, with `length(rest)=r`.

- If `y>r`, emit `0`.
- Otherwise compute bit `y` of `C`. If it is one, play the positive H-game
  for `p` with environment `[y]` along `rest`. If it is zero, use the aligned
  negative game. Emit the **negation** of that finite Boolean result.

In particular, `0` is the observer's winning value. The first move `C` is a
proposed finite truth table, and the second, universal move `y` challenges one
of its bits. The timeout convention ensures a short game cannot incorrectly
refute a true signed formula. No move bound is imposed by the observer;
`y>r` is an explicit branch of the selected finite payoff function.

The exact definitions are `Truth`, `path`, `aligned`, and `selectedValue` in
[M236Game](formalization/lean/PASoundness/M236Game.lean). The small Python
[reference](formalization/bindings/m236/semantic_reference.py) is useful for
finite experimentation but is not the formal proof.

## 2. Why all finite games capture finite truth tables

Let `T(f,[y])` be the standard semantic truth of the H-formula above. The key
intermediate property is

```math
\begin{gathered}
\forall f,A\in\mathbb N\ \exists C\in\mathbb N\ \forall y\le A,
\\
\qquad \mathrm{bit}(C,y)=1\ \Longleftrightarrow\ T(f,[y]).
\end{gathered}
\tag{FT}
```

A new finite `C` may be chosen for each formula and bound. This is not a single
truth set for all formulas and values.

The finite-path lemma is proved by induction on the formula code:

- If a signed formula is true, its player wins every finite truncation, since
  a timeout is optimistic.
- With at least `f+1` slots the path game is exact; with the possible alignment
  slot, `f+2` suffices. Children strictly decrease, so the inductive bound
  applies after an H-move. At atoms the paid slot is essential.

Consequently, if all selected rank games are won, fix `f,A` and take
`r=A+f+2`. The winning rank-`r+2` game first provides a number `C`. Against
any challenge `y≤A≤r`, its remaining exact game forces the `y`th bit of `C`
to agree with `T(f,[y])`. This proves (FT).

Conversely, at rank `r+2`, choose the finite table supplied by (FT) for `f=p`
and bound `r`. Every supported challenge chooses a true signed formula, which
wins even if truncated. Unsupported challenges win by the explicit zero-payoff
branch. Rank one is trivial. This gives every required strategy.

The source scheduler is fair and its value function is total and deterministic,
so every legal address is printed, duplicates agree, parsing succeeds, and
each finite source step ends at a frame boundary. Hence the guards are proved
independently of soundness. The result is
`selected_source_accept_iff_finite_tables` in
[M236Game](formalization/lean/PASoundness/M236Game.lean).

## 3. From finite tables to a compact proof calculus

The intermediate calculus **K** has explicitly defined numeric formulas,
nine axiom selectors and finite derivation constructors. Its provability is
syntactic: it does not mean truth and is not defined as PA provability.
The standard model interprets numbers as finite binary-coded sets.

The formal proof first translates (FT) into parameterized finite-support
comprehension, retaining arbitrary finite environments and parameters.
Pointed support allows a finite set `A` and a distinguished point `B`:
there exists a finite set `C` containing only elements satisfying the chosen
predicate, and containing every satisfying element of `A∪{B}`.
Finite masks, adding a singleton support bit, and capture-safe weakening prove
the changes of presentation. See
[M236Definitions](formalization/lean/PASoundness/M236Definitions.lean),
[M236Positional](formalization/lean/PASoundness/M236Positional.lean), and
[M236Named](formalization/lean/PASoundness/M236Named.lean).

This is exactly the semantic content needed for K's ninth selector, including
its variable-collision guard. The other eight selectors are shown valid
directly. Induction on finite K derivations now proves K soundness from the
game family: truth and axiom cases, universal generalization, and modus ponens.
In the reverse direction, K soundness supplies the ninth axiom's truth; a
fresh-variable translation and double-negation padding recover pointed support
and then (FT). Thus

```math
\begin{gathered}
\mathrm{TraceAccept}(\mathrm{Source}(\mathrm{selectedValue}))
\\
\quad\Longleftrightarrow\quad\mathrm{CompactSound}.
\end{gathered}
```

The exact result is `source_accept_iff_compact_sound` in
[M236Reverse](formalization/lean/PASoundness/M236Reverse.lean).
It does not use an independent proof of full K soundness as a shortcut.

## 4. From that source to these 472 physical transitions

A source-level equivalence is not enough. The physical proof keeps the following
boundaries explicit:

1. **Literal bytes and quotient.** The selected and raw tables are transcribed
   into Lean; Lean proves serialization equalities with the embedded files,
   including event labels, and the raw-to-selected quotient preserves every
   output word. The Python transcriber and hash checks are not the equality
   proof. See `M236TableRowsConnect`, `M236TableTextSelected`,
   `M236TableTextRaw`, and `M236Quotient`.
2. **Blank start and runtime graph.** The blank initializer reaches the stated
   runtime boundary after 89,821,408 physical steps with no output. A checked
   occurrence graph and tape/register relations preserve the actual ordered
   wire, with positive finite progress. `graph_traceAccept_iff` in `M236GraphFullObserver`
   transfers the whole guarded observer, not just eventual record membership.
3. **Every scheduler stage.** The proof covers rank-one frames, in-budget
   evaluation, and overflow frames for arbitrary stage and reserve. It verifies
   address extraction, unary output, finite environment operations, signed
   formula descent, atom evaluation, cleanup and return to the next stage.
   `scheduler_all_frame_blocks` discharges all cases; it does not retain a
   user-supplied “covered stages” assumption.
4. **Cofinal ordered refinement.** `sourceMachineRefinement` relates every
   source step to a positive finite block of literal machine steps, with exactly
   the same ordered output. Positive progress prevents infinitely many abstract
   stages from being hidden in finitely many physical steps. Frame progress
   is transferred explicitly as well.

The final physical composition is in
[M236SchedulerRefinement](formalization/lean/PASoundness/M236SchedulerRefinement.lean).
It yields `scheduler_machine_trace_iff_source`; combined with the preceding
section, [M236MachineCompact](formalization/lean/PASoundness/M236MachineCompact.lean)
yields the literal machine/compact-soundness equivalence.

Reproducing the Python builder is complementary evidence of the historical
construction. The Lean proof checks the fixed table and graph, rather than
trusting a general Python compiler theorem. A finite literal replay checks a
finite prefix only and cannot replace the all-time simulation.

## 5. Why this really is PA soundness

[Peano](formalization/lean/PASoundness/Peano.lean) specifies ordinary first-order
PA: zero, successor, addition and multiplication, equality logic, the six usual
arithmetic axiom families, and full induction for arbitrary formulas including
parameters. `Peano.Proves` is syntactic derivability; `Nat ⊨ s` is satisfaction
in the standard natural-number structure. This is all-sentence soundness,
not merely consistency or a fixed quantifier-fragment soundness statement.

The two translations are separate obligations.

**PA soundness implies K soundness.** A finite K derivation is sent to an actual
PA derivation of its arithmetic interpretation. Binary membership is defined
arithmetically. Translated falsity and the full parameterized comprehension
family are derived *inside PA*, using finite coding, arithmetic induction and
beta-coded sequence constructions. They are not inferred merely from their
truth in standard `Nat`. Universal closure handles arbitrary assignments, and
a separate theorem proves that the interpretation preserves and reflects truth.
The closed interfaces are in
[PeanoCompactProofToPAClosed](formalization/lean/PASoundness/PeanoCompactProofToPAClosed.lean)
and [PASoundnessToM236Closed](formalization/lean/PASoundness/PASoundnessToM236Closed.lean).

**K soundness implies PA soundness.** A supplied checked PA proof is translated
into finite K derivation data. The translation represents natural numbers by
finite-ordinal candidates, represents arithmetic operations by formulas, and
uses candidate-domain guards for free variables. All logical axioms, all six
arithmetic families, full induction, modus ponens and generalization have
handlers in the final construction. Truth preservation is proved separately
on ordinal-coded assignments. Domain guards are essential: the old unguarded
open-formula handler interface is refuted by an explicit counterexample and is
not used to close the theorem.

The exported
[PAtoCompactEndToEndProofTranslation](formalization/lean/PASoundness/PAtoCompactEndToEndProofTranslation.lean)
provides `translateChecked`, `translated_certificate`,
`guarded_translation_truth`, `compact_derivation_to_pa`, and
`compact_translation_truth`. It then states
`selected_accepts_iff_pa_soundness` without extra bridge parameters.
The proof-data constructors use classical choice. Although their outputs are
finite derivation data, no executable extractor from arbitrary Prop-valued PA
derivability is claimed.

Combining Sections 2–5 gives the stated equivalence. The
[axiom/dependency audit](formalization/lean/PASoundness/Audit.lean) checks the
structural endpoints for forbidden dependencies on the project's independent
PA/K soundness and comprehension theorems. See [VERIFICATION.md](VERIFICATION.md)
for the exact audited axioms, reported revisions, and checks actually rerun for
this publication.

## 6. Reading the preserved source

The formal source is copied unchanged from the final source revision. Some
module comments describe what that particular intermediate file did not yet
prove; older interfaces may still have explicit assumptions. Those comments do
not override the later closed endpoint. Start with the end-to-end module and
follow its imports when checking the current theorem.

No claim is made that the old PA238, PA804 or PA926 physical machines have this
same endpoint, or that their encodings coincide with M236's. Some such sources
remain in the preserved full project because its aggregate and audits include
historical interface tests. The theorem here is only about the pinned M236.
