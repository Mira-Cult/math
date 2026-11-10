import PASoundness.PAtoCompactFilteredSubset
import PASoundness.PAtoCompactVariableInstance
import PASoundness.PAtoCompactTransitiveWitness

/-! Literal K construction of a nonempty filtered counterexample set.
Code 1 is literally `member 0 0`; ordinary negation and existence readings
are justified separately in standard HF semantics. No leastness or induction
is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCounterexampleSet
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactVariableInstance PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactFilteredSubset

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The quantifier-free graph shell with the original, possibly quantified,
named formula f in predicate position. -/
def namedCounterexampleGraphBody (x t : Nat) (f : CompactNamed.Formula) : CompactNamed.Formula :=
  let c := filterPredicate x t (neg f.encode)
  let pred := namedBoth (.member x t) f.not
  namedBoth (.imp (.member c t) pred) (.imp pred (.member c t))

/-- Instantiation at the explicit counterexample name. The replacement and
test names avoid all binders of f, preventing capture. -/
def counterexample_graph_at (x t a : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hta : t ≠ a) (htf : t ∉ f.binders) (haf : a ∉ f.binders) :
    let c := filterPredicate x t (neg f.encode)
    let inst := (CompactNamed.replace t a f).encode
    KDerivation (imp (filterGraph x c t (neg f.encode))
      (both (imp (member c a) (both (member x a) (neg inst)))
        (imp (both (member x a) (neg inst)) (member c a)))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  have hc := filterPredicate_bounds x t (neg f.encode)
  have htc : t ≠ c := by dsimp [c]; omega
  have hct' : imp (imp (member x t) (imp (imp f.encode 1) 1)) 1 ≠ t := by
    change c ≠ t
    exact Ne.symm htc
  let body := namedCounterexampleGraphBody x t f
  have hu := CompactNamed.universalInstance t a body hta
    (by simpa [body, namedCounterexampleGraphBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.binders] using htf)
    (by simpa [body, namedCounterexampleGraphBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.binders] using haf)
  simpa [body, namedCounterexampleGraphBody, namedBoth, CompactNamed.Formula.not,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename, filterGraph,
    filterPredicate, CompactProof.both, CompactProof.neg,
    hxt, htc, hct', hta, Ne.symm hxt, Ne.symm htc, Ne.symm hta] using hu

/-- The explicit element a supplies a nonempty witness once it is known to
belong to the filtered graph. a must differ from the set name c, so the
existential binds only the element occurrence. -/
def counterexample_nonempty_intro (c a : Nat) (_hca : c ≠ a) :
    KDerivation (imp (member c a) (existsCode a (member c a))) := by
  have hi := CompactNamed.existsIntroduce a (.member c a) (by simp [CompactNamed.Formula.binders])
  exact hi

/-- From an explicit counterexample a, selector 8 constructs a filtered set
whose graph is exact and whose membership is nonempty. The fresh-name
conditions are stated on f and the computed selector witness c; they do not
assume a represented least element or induction. -/
def nonempty_counterexample_filter (x t a : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hta : t ≠ a) (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hca : filterPredicate x t (neg f.encode) ≠ a)
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names) :
    let c := filterPredicate x t (neg f.encode)
    let inst := (CompactNamed.replace t a f).encode
    KDerivation (imp (member x a) (imp (neg inst)
      (existsCode c (both (filterGraph x c t (neg f.encode))
        (existsCode a (member c a)))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let instF := CompactNamed.replace t a f
  let X := member x a
  let N := neg instF.encode
  let G := filterGraph x c t (neg f.encode)
  let E := existsCode a (member c a)
  let Γ := [N, X]
  have hc := filterPredicate_bounds x t (neg f.encode)
  have hcx : c ≠ x := by dsimp [c]; omega
  have hct : c ≠ t := by dsimp [c]; omega
  have hcInst : c ∉ instF.names := by
    intro hm
    have he := CompactNamed.replace_names_outside t a c f hct hca
    exact hcf (he.mp hm)
  let fN : CompactNamed.Formula := instF.not
  have hnames : c ∉ fN.names := by simpa [fN, CompactNamed.Formula.not, CompactNamed.Formula.names] using hcInst
  have hvN : KDerivation (imp N (allCode c N)) := by
    have h := fN.vacuity c hnames
    simpa [fN, N, CompactNamed.Formula.not, CompactNamed.Formula.encode, CompactProof.neg] using h
  have hvX : KDerivation (imp X (allCode c X)) := membershipVacuity x a c hcx hca
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode c h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = N
    · subst h
      exact hvN
    · have he' : h = X := hh.resolve_left he
      subst h
      exact hvX
  have hX : Context Γ X := .hypothesis (by simp [Γ])
  have hN : Context Γ N := .hypothesis (by simp [Γ])
  have hstep : Context Γ (imp G (both G E)) := by
    apply Context.deduction
    have hg : Context (G :: Γ) G := Context.head Γ G
    have heq := Context.mp hg (.closed (counterexample_graph_at x t a f hxt hta htf haf))
    have hback : Context (G :: Γ) (imp (both X N) (member c a)) := Context.conjunctionRight heq
    have htest : Context (G :: Γ) (both X N) :=
      Context.conjunctionIntro (Context.under hX G) (Context.under hN G)
    have hm : Context (G :: Γ) (member c a) := .mp htest hback
    have hne : Context (G :: Γ) E := .mp hm (.closed (counterexample_nonempty_intro c a hca))
    exact Context.conjunctionIntro hg hne
  have hall : Context Γ (allCode c (imp G (both G E))) := Context.generalize c hv hstep
  have hex : Context Γ (existsCode c G) := .closed (filtered_subset_exists x t (neg f.encode) hxt)
  have hresult : Context Γ (existsCode c (both G E)) := exists_map_context hall hex
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hresult

theorem nonempty_counterexample_filter_certificate (x t a : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hta : t ≠ a) (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hca : filterPredicate x t (neg f.encode) ≠ a)
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names) :
    let c := filterPredicate x t (neg f.encode)
    let inst := (CompactNamed.replace t a f).encode
    theoremCode (certificate (nonempty_counterexample_filter x t a f hxt hta htf haf hca hcf)) =
      imp (member x a) (imp (neg inst)
        (existsCode c (both (filterGraph x c t (neg f.encode)) (existsCode a (member c a))))) :=
  certificate_correct (nonempty_counterexample_filter x t a f hxt hta htf haf hca hcf)

/-- Separate standard-HF interpretation of the explicit named predicate
instance, including capture-safe replacement. This is not used by the K
proof construction. -/
theorem counterexample_instance_standard (t a : Nat) (f : CompactNamed.Formula)
    (htf : t ∉ f.binders) (haf : a ∉ f.binders) (ρ : CompactMatrix.Environment) :
    (CompactMatrix.decode (neg (CompactNamed.replace t a f).encode)).Realize ρ ↔
      ¬ f.Realize (CompactMatrix.update ρ t (ρ a)) := by
  rw [CompactSemantics.realize_neg, CompactNamed.Formula.encode_realize,
    CompactNamed.replace_realize t a f htf haf ρ]

end PASoundness.PAtoCompactCounterexampleSet
