import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactAdjunction

/-! Conditional top-source witness for the new bijection clause. The source
and target successor, new-pair/new-graph, clean old-graph, encoded source
irreflexivity, and uniform edge split remain explicit hypotheses. The three
bounded witness/uniqueness derivations are explicit K proof-data parameters;
no collection, model soundness or quotient theorem is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccLeftTopCase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactSuccCongruenceData
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def namedSplit : Formula := .all 28 (.all 29
  (.imp (graphFormula 9 28 29)
    (namedEither (graphFormula 6 28 29) (namedBoth (.equal 28 0) (.equal 29 1)))))
def uniformSplit : Nat := namedSplit.encode

def topSplit : Nat := imp (graphFormula 9 0 4).encode
  (either (graphFormula 6 0 4).encode (both (equal 0 0) (equal 4 1)))

/-- Capture-safe specialization of the supplied uniform edge split. -/
def uniform_split_at_top : KDerivation (imp uniformSplit topSplit) := by
  let f : Formula := .imp (graphFormula 9 28 29)
    (namedEither (graphFormula 6 28 29) (namedBoth (.equal 28 0) (.equal 29 1)))
  let f0 : Formula := .imp (graphFormula 9 0 29)
    (namedEither (graphFormula 6 0 29) (namedBoth (.equal 0 0) (.equal 29 1)))
  have h2 := CompactNamed.universalInstance 28 0 (.all 29 f)
    (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 28 0 (.all 29 f) = .all 29 f0 := by decide
  rw [hr2] at h2
  have h3 := CompactNamed.universalInstance 29 4 f0
    (by decide) (by decide) (by decide)
  have hr3 : CompactNamed.replace 29 4 f0 =
      .imp (graphFormula 9 0 4)
        (namedEither (graphFormula 6 0 4) (namedBoth (.equal 0 0) (.equal 4 1))) := by decide
  rw [hr3] at h3
  exact compose h2 h3

def witnessBody : Formula := namedBoth (.member 8 3) (namedBoth (graphFormula 9 2 3)
  (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 9 2 4)) (.equal 4 3))))

def witnessAtOne : Formula := namedBoth (.member 8 1) (namedBoth (graphFormula 9 2 1)
  (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 9 2 4)) (.equal 4 1))))

/-- Pointwise top-source case, conditional on the displayed K derivations for
endpoint existence and old-edge exclusion. No premise is discharged by model
soundness, and code 1 keeps its literal compact meaning. -/
def top_case
    (hTarget : KDerivation (imp targetSuccessor (member 8 1)))
    (hGraph : KDerivation (imp newGraph (imp newPair (graphFormula 9 0 1).encode)))
    (hUnique : KDerivation (imp cleanGraph (imp sourceIrreflexive
      (imp topSplit (imp (graphFormula 9 0 4).encode (equal 4 1)))))) :
    KDerivation (imp cleanGraph (imp sourceIrreflexive (imp uniformSplit
      (imp targetSuccessor (imp newGraph (imp newPair
        (imp (equal 2 0) (existsCode 3 witnessBody.encode)))))))) := by
  let C := cleanGraph
  let R := sourceIrreflexive
  let H := uniformSplit
  let T := targetSuccessor
  let G := newGraph
  let P := newPair
  let E := equal 2 0
  let Γ := [E,H,R,C]
  let Δ := [E,P,G,T,H,R,C]
  let U := both (member 8 4) (graphFormula 9 2 4).encode
  let cleanNamed : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 0 1))
  have hvC : KDerivation (imp C (allCode 4 C)) := by
    have h := cleanNamed.vacuity 4 (by decide)
    simpa [C, cleanGraph, cleanNamed, Formula.encode] using h
  have hvR : KDerivation (imp R (allCode 4 R)) := by
    have h := (Formula.not (.member 0 0)).vacuity 4 (by decide)
    simpa [R, sourceIrreflexive, Formula.not, Formula.encode, CompactProof.neg] using h
  have hvH : KDerivation (imp H (allCode 4 H)) := namedSplit.vacuity 4 (by decide)
  have hvE : KDerivation (imp E (allCode 4 E)) := equalityVacuity 2 0 4 (by decide) (by decide)
  have hreplace := (CompactNamed.equalityReplace 2 0 (graphFormula 9 2 4)
    (by decide) (by decide)).1
  have hreplaceSyntax : CompactNamed.replace 2 0 (graphFormula 9 2 4) = graphFormula 9 0 4 := by decide
  rw [hreplaceSyntax] at hreplace
  have huniqLocal : Context Γ (imp U (equal 4 1)) := by
    apply Context.deduction
    have hu : Context (U :: Γ) U := Context.head Γ U
    have he : Context (U :: Γ) E := .hypothesis (by simp [Γ])
    have hh : Context (U :: Γ) H := .hypothesis (by simp [Γ])
    have hr : Context (U :: Γ) R := .hypothesis (by simp [Γ])
    have hc : Context (U :: Γ) C := .hypothesis (by simp [Γ])
    have hg : Context (U :: Γ) (graphFormula 9 2 4).encode := Context.conjunctionRight hu
    have hg0 : Context (U :: Γ) (graphFormula 9 0 4).encode := .mp hg (.mp he (.closed hreplace))
    have hs : Context (U :: Γ) topSplit := .mp hh (.closed uniform_split_at_top)
    exact .mp hg0 (.mp hs (.mp hr (.mp hc (.closed hUnique))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = E
    · subst h; exact hvE
    · by_cases hH : h = H
      · subst h; exact hvH
      · by_cases hR : h = R
        · subst h; exact hvR
        · have hC : h = C := ((hh.resolve_left he).resolve_left hH).resolve_left hR
          subst h; exact hvC
  have huniq : Context Γ (allCode 4 (imp U (equal 4 1))) :=
    Context.generalize 4 hv huniqLocal
  have hgraphReplace := (CompactNamed.equalityReplace 0 2 (graphFormula 9 0 1)
    (by decide) (by decide)).1
  have hgraphSyntax : CompactNamed.replace 0 2 (graphFormula 9 0 1) = graphFormula 9 2 1 := by decide
  rw [hgraphSyntax] at hgraphReplace
  have hex := exists_variable_intro 3 1 witnessBody (by decide) (by decide) (by decide)
  have hexSyntax : CompactNamed.replace 3 1 witnessBody = witnessAtOne := by decide
  rw [hexSyntax] at hex
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have he : Context Δ E := .hypothesis (by simp [Δ])
  have hp : Context Δ P := .hypothesis (by simp [Δ])
  have hg : Context Δ G := .hypothesis (by simp [Δ])
  have ht : Context Δ T := .hypothesis (by simp [Δ])
  have hm : Context Δ (member 8 1) := .mp ht (.closed hTarget)
  have hp0 : Context Δ (graphFormula 9 0 1).encode := .mp hp (.mp hg (.closed hGraph))
  have hp2 : Context Δ (graphFormula 9 2 1).encode := .mp hp0 (.mp (Context.eqSymm he) (.closed hgraphReplace))
  have hu : Context Δ (allCode 4 (imp U (equal 4 1))) :=
    Context.weaken huniq (by
      intro h hh
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
      simp only [Δ, List.mem_cons, List.not_mem_nil, or_false]
      tauto)
  have hbody : Context Δ witnessAtOne.encode := Context.conjunctionIntro hm (Context.conjunctionIntro hp2 hu)
  exact .mp hbody (.closed hex)

theorem top_case_certificate
    (hTarget : KDerivation (imp targetSuccessor (member 8 1)))
    (hGraph : KDerivation (imp newGraph (imp newPair (graphFormula 9 0 1).encode)))
    (hUnique : KDerivation (imp cleanGraph (imp sourceIrreflexive
      (imp topSplit (imp (graphFormula 9 0 4).encode (equal 4 1)))))) :
    theoremCode (certificate (top_case hTarget hGraph hUnique)) =
      imp cleanGraph (imp sourceIrreflexive (imp uniformSplit
        (imp targetSuccessor (imp newGraph (imp newPair
          (imp (equal 2 0) (existsCode 3 witnessBody.encode))))))) :=
  certificate_correct (top_case hTarget hGraph hUnique)

end PASoundness.PAtoCompactSuccLeftTopCase

#print axioms PASoundness.PAtoCompactSuccLeftTopCase.top_case
#print axioms PASoundness.PAtoCompactSuccLeftTopCase.top_case_certificate
