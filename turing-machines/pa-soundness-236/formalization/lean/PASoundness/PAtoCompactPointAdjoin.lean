import PASoundness.PAtoCompactPointAdjoinSelector

/-! Adjoining one supplied point to a supplied represented K container. The
construction is finite K proof data, not replacement, product collection,
or the creation of arbitrary isomorphism graphs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPointAdjoin
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPointAdjoinSelector
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def adjoinCode (x p s q : Nat) : Nat :=
  allCode q (both (imp (member s q) (either (equal q p) (member x q)))
    (imp (either (equal q p) (member x q)) (member s q)))

def namedAdjoin (x p s q : Nat) : CompactNamed.Formula :=
  .all q (namedBoth (.imp (.member s q) (namedEither (.equal q p) (.member x q)))
    (.imp (namedEither (.equal q p) (.member x q)) (.member s q)))

def namedPredicate (x p t : Nat) : CompactNamed.Formula :=
  namedEither (.equal t p) (.member x t)

def namedInner (x p t : Nat) : CompactNamed.Formula :=
  let c := adjoinPredicate x p t
  namedBoth (.imp (.member x t) (.imp (namedPredicate x p t) (.member c t)))
    (.imp (.member c t) (namedPredicate x p t))

def namedBody (x p t : Nat) : CompactNamed.Formula :=
  let c := adjoinPredicate x p t
  namedBoth (.all t (namedInner x p t)) (.imp (namedPredicate x p t) (.member c t))

/-- Instantiation of the selector's quantified interior. -/
def adjoin_inner_instance (x p t q : Nat)
    (htx : t ≠ x) (htp : t ≠ p) (htq : t ≠ q) :
    KDerivation (imp (allCode t (namedInner x p t).encode)
      (both (imp (member x q) (imp (adjoinPredicate x p q) (member (adjoinPredicate x p t) q)))
        (imp (member (adjoinPredicate x p t) q) (adjoinPredicate x p q)))) := by
  have hc := PAtoCompactPointAdjoinSelector.predicate_names_lt x p t
  have htc : t ≠ adjoinPredicate x p t := by omega
  have hct : adjoinPredicate x p t ≠ t := by omega
  have hct' : imp (imp (equal t p) 1) (member x t) ≠ t := hct
  have h := CompactNamed.universalInstance t q (namedInner x p t) htq
    (by simp [namedInner, namedPredicate, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [namedInner, namedPredicate, namedBoth, namedEither, CompactNamed.Formula.binders])
  simpa [namedInner, namedPredicate, namedBoth, namedEither, adjoinPredicate,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    htx, htp, htq, htc, hct, hct', Ne.symm htx, Ne.symm htp, Ne.symm htq, Ne.symm htc] using h

/-- The selected body and t=p imply the exact pointwise union property. -/
def adjoin_pointwise (x p t q : Nat) (htx : t ≠ x) (htp : t ≠ p) (htq : t ≠ q) :
    KDerivation (imp (adjoinBody x p t) (imp (equal t p)
      (both (imp (member (adjoinPredicate x p t) q) (adjoinPredicate x p q))
        (imp (adjoinPredicate x p q) (member (adjoinPredicate x p t) q))))) := by
  let c := adjoinPredicate x p t
  let P := adjoinPredicate x p q
  let B := adjoinBody x p t
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal t p,B]
  have he : Context Γ (equal t p) := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hbound : Context Γ (allCode t (namedInner x p t).encode) := by
    have hh := Context.conjunctionLeft hb
    simpa [B, adjoinBody, adjoinPredicate, namedInner, namedPredicate, namedBoth, namedEither,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hh
  have hi := Context.mp hbound (.closed (adjoin_inner_instance x p t q htx htp htq))
  have hforward : Context Γ (imp (member c q) P) := Context.conjunctionRight hi
  have hpositive : Context Γ (imp (member x q) (imp P (member c q))) := Context.conjunctionLeft hi
  have hcp : Context Γ (member c p) := by
    have houter : Context Γ (imp c (member c t)) := Context.conjunctionRight hb
    have hpred : Context Γ c := Context.disjunctionLeft (b := member x t) he
    exact .mp he (.mp (.mp hpred houter) (.closed (memberRightEquality c t p)))
  have hreverse : Context Γ (imp P (member c q)) := by
    apply Context.deduction
    have hP : Context (P :: Γ) P := Context.head Γ P
    apply Context.disjunctionElim hP
    · have heq : Context (equal q p :: P :: Γ) (equal q p) := Context.head _ _
      have hm : Context (equal q p :: P :: Γ) (member c p) := Context.under (Context.under hcp P) _
      exact .mp (Context.eqSymm heq) (.mp hm (.closed (memberRightEquality c p q)))
    · have hm : Context (member x q :: P :: Γ) (member x q) := Context.head _ _
      exact .mp (Context.under (Context.head Γ P) _) (.mp hm (Context.under (Context.under hpositive P) _))
  exact Context.conjunctionIntro hforward hreverse

/-- Explicit body-to-graph K derivation. The container and point names x,p
may coincide; only the quantified names must be fresh. -/
def adjoin_body_graph (x p t q : Nat)
    (htx : t ≠ x) (htp : t ≠ p) (hqt : q ≠ t)
    (hqx : q ≠ x) (hqp : q ≠ p) (hqc : q ≠ adjoinPredicate x p t) :
    KDerivation (imp (adjoinBody x p t)
      (imp (equal t p) (adjoinCode x p (adjoinPredicate x p t) q))) := by
  let c := adjoinPredicate x p t
  let B := adjoinBody x p t
  let E := equal t p
  let Γ := [E,B]
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (both (imp (member c q) (adjoinPredicate x p q))
      (imp (adjoinPredicate x p q) (member c q))) :=
    .mp he (.mp hb (.closed (adjoin_pointwise x p t q htx htp (Ne.symm hqt))))
  let fB := namedBody x p t
  have hnamesB : q ∉ fB.names := by
    simp [fB, namedBody, namedInner, namedPredicate, namedBoth, namedEither,
      CompactNamed.Formula.names, hqx, hqp, hqt, hqc]
  have hvB : KDerivation (imp B (allCode q B)) := by
    have h := fB.vacuity q hnamesB
    simpa [fB, B, namedBody, namedInner, namedPredicate, namedBoth, namedEither,
      adjoinBody, adjoinPredicate, CompactNamed.Formula.encode, CompactProof.both,
      CompactProof.neg, CompactDerivations.either] using h
  have hvE : KDerivation (imp E (allCode q E)) := equalityVacuity t p q hqt hqp
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode q h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he' : h = E
    · subst h; exact hvE
    · have hb' : h = B := hh.resolve_left he'
      subst h; exact hvB
  have hg : Context Γ (adjoinCode x p c q) := by
    have h := Context.generalize q hv hpoint
    simpa [adjoinCode, adjoinPredicate] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hg

theorem adjoin_body_graph_certificate (x p t q : Nat)
    (htx : t ≠ x) (htp : t ≠ p) (hqt : q ≠ t)
    (hqx : q ≠ x) (hqp : q ≠ p) (hqc : q ≠ adjoinPredicate x p t) :
    theoremCode (certificate (adjoin_body_graph x p t q htx htp hqt hqx hqp hqc)) =
      imp (adjoinBody x p t) (imp (equal t p) (adjoinCode x p (adjoinPredicate x p t) q)) :=
  certificate_correct (adjoin_body_graph x p t q htx htp hqt hqx hqp hqc)

/-- Introduce the concrete selector witness in a fresh existential binder. -/
def adjoin_existential_intro (x p c d q : Nat)
    (hcd : c ≠ d) (hdx : d ≠ x) (hdp : d ≠ p) (hcq : c ≠ q) (hdq : d ≠ q) :
    KDerivation (imp (adjoinCode x p c q) (existsCode d (adjoinCode x p d q))) := by
  let f := namedAdjoin x p d q
  have h := exists_variable_intro d c f (Ne.symm hcd)
    (by simp [f, namedAdjoin, namedBoth, namedEither, CompactNamed.Formula.binders, hdq])
    (by simp [f, namedAdjoin, namedBoth, namedEither, CompactNamed.Formula.binders, hcq])
  simpa [f, namedAdjoin, namedBoth, namedEither, adjoinCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hcd, hdx, hdp, hcq, hdq, Ne.symm hcd, Ne.symm hdx, Ne.symm hdp, Ne.symm hcq, Ne.symm hdq] using h

/-- Exact existential adjunction under explicit name-freshness constraints. -/
def adjoin_graph_exists_fresh (x p t q d : Nat)
    (htx : t ≠ x) (htp : t ≠ p) (hqt : q ≠ t) (hqx : q ≠ x) (hqp : q ≠ p)
    (hqc : q ≠ adjoinPredicate x p t) (hdx : d ≠ x) (hdp : d ≠ p)
    (hdt : d ≠ t) (hdq : d ≠ q) (hdc : d ≠ adjoinPredicate x p t) :
    KDerivation (existsCode d (adjoinCode x p d q)) := by
  let c := adjoinPredicate x p t
  let E := existsCode d (adjoinCode x p d q)
  let fE : CompactNamed.Formula := .ex d (namedAdjoin x p d q)
  let fGoal : CompactNamed.Formula := .imp (.equal t p) fE
  have hc := PAtoCompactPointAdjoinSelector.predicate_names_lt x p t
  have hcx : c ≠ x := by dsimp [c]; omega
  have hcp : c ≠ p := by dsimp [c]; omega
  have hct : c ≠ t := by dsimp [c]; omega
  have hcq : c ≠ q := Ne.symm hqc
  have hcd : c ≠ d := Ne.symm hdc
  have hnamesC : c ∉ fGoal.names := by
    simp [fGoal, fE, namedAdjoin, namedBoth, namedEither, CompactNamed.Formula.names,
      hcx, hcp, hct, hcq, hcd]
  have hvC : KDerivation (imp (imp (equal t p) E) (allCode c (imp (equal t p) E))) := by
    have h := fGoal.vacuity c hnamesC
    simpa [fGoal, fE, E, namedAdjoin, namedBoth, namedEither, adjoinCode,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h
  have hbody : KDerivation (imp (adjoinBody x p t) (imp (equal t p) E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [equal t p, adjoinBody x p t]
    have he : Context Γ (equal t p) := .hypothesis (by simp [Γ])
    have hb : Context Γ (adjoinBody x p t) := .hypothesis (by simp [Γ])
    have hs : Context Γ (adjoinCode x p c q) :=
      .mp he (.mp hb (.closed (adjoin_body_graph x p t q htx htp hqt hqx hqp hqc)))
    exact .mp hs (.closed (adjoin_existential_intro x p c d q hcd hdx hdp hcq hdq))
  have hcond : KDerivation (imp (equal t p) E) := by
    apply Context.closeEmpty
    apply Context.existsElim hvC
    · exact .closed (.generalize c hbody)
    · exact .closed (selector8_adjoin_witness_closed x p t)
  have hnamesT : t ∉ fE.names := by
    simp [fE, namedAdjoin, namedBoth, namedEither, CompactNamed.Formula.names,
      htx, htp, Ne.symm hdt, Ne.symm hqt]
  have hvT : KDerivation (imp E (allCode t E)) := by
    have h := fE.vacuity t hnamesT
    simpa [fE, E, namedAdjoin, namedBoth, namedEither, adjoinCode,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h
  apply Context.closeEmpty
  apply Context.existsElim hvT
  · exact .closed (.generalize t hcond)
  · exact .closed (existsEqual t p)

/-- K constructs x ∪ {p}, for any input names x,p including x=p. -/
def adjoin_graph_exists (x p : Nat) :
    let t := max x p + 1
    let c := adjoinPredicate x p t
    let q := c+1
    let d := q+1
    KDerivation (existsCode d (adjoinCode x p d q)) := by
  dsimp only
  let t := max x p + 1
  let c := adjoinPredicate x p t
  let q := c+1
  let d := q+1
  have hc := PAtoCompactPointAdjoinSelector.predicate_names_lt x p t
  have htx : t ≠ x := by dsimp [t]; omega
  have htp : t ≠ p := by dsimp [t]; omega
  have hqt : q ≠ t := by dsimp [q,c]; omega
  have hqx : q ≠ x := by dsimp [q,c]; omega
  have hqp : q ≠ p := by dsimp [q,c]; omega
  have hqc : q ≠ adjoinPredicate x p t := by dsimp [q,c]; omega
  have hdx : d ≠ x := by dsimp [d,q,c]; omega
  have hdp : d ≠ p := by dsimp [d,q,c]; omega
  have hdt : d ≠ t := by dsimp [d,q,c]; omega
  have hdq : d ≠ q := by dsimp [d,q]; omega
  have hdc : d ≠ adjoinPredicate x p t := by dsimp [d,q,c]; omega
  exact adjoin_graph_exists_fresh x p t q d htx htp hqt hqx hqp hqc hdx hdp hdt hdq hdc

theorem adjoin_graph_exists_certificate (x p : Nat) :
    let t := max x p + 1
    let c := adjoinPredicate x p t
    let q := c+1
    let d := q+1
    theoremCode (certificate (adjoin_graph_exists x p)) = existsCode d (adjoinCode x p d q) :=
  certificate_correct (adjoin_graph_exists x p)

end PASoundness.PAtoCompactPointAdjoin

#print axioms PASoundness.PAtoCompactPointAdjoin.adjoin_body_graph
#print axioms PASoundness.PAtoCompactPointAdjoin.adjoin_body_graph_certificate
#print axioms PASoundness.PAtoCompactPointAdjoin.adjoin_graph_exists
#print axioms PASoundness.PAtoCompactPointAdjoin.adjoin_graph_exists_certificate
