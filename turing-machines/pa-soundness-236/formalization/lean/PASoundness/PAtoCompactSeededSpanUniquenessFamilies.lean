import PASoundness.PAtoCompactSeededSpanGlobalUniqueness
import PASoundness.PAtoCompactConditionalTransitivityTargetAll
import PASoundness.PAtoCompactConditionalTransitivitySourceAll

/-! Extract the exact target- and source-uniqueness families used by the
literal graph9 bijection clauses from the supplied quantified pointwise
uniqueness relation. Coverage and the relation itself remain separate inputs. -/
namespace PASoundness.PAtoCompactSeededSpanUniquenessFamilies

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSeededSpanGlobalUniqueness
open PASoundness.PAtoCompactConditionalTransitivityTargetAll

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def targetPoint : Formula := replace 27 5 (replace 26 2 pointClause)
private def sourcePoint : Formula := replace 27 3 (replace 26 4 pointClause)

private def target_instance : KDerivation (imp quantifiedUniqueness.encode targetPoint.encode) := by
  have h2 := allSpecialize 2 (.all 26 (.all 3 (.all 27 pointClause))) (by decide)
  have h26 := universalInstance 26 2 (.all 3 (.all 27 pointClause)) (by decide) (by decide) (by decide)
  have ha26 : replace 26 2 (.all 3 (.all 27 pointClause)) =
      .all 3 (.all 27 (replace 26 2 pointClause)) := by decide
  rw [ha26] at h26
  have h3 := allSpecialize 3 (.all 27 (replace 26 2 pointClause)) (by decide)
  have h27 := universalInstance 27 5 (replace 26 2 pointClause) (by decide) (by decide) (by decide)
  simpa only [quantifiedUniqueness,targetPoint,Formula.encode] using compose h2 (compose h26 (compose h3 h27))

private def source_instance : KDerivation (imp quantifiedUniqueness.encode sourcePoint.encode) := by
  have h2 := allSpecialize 2 (.all 26 (.all 3 (.all 27 pointClause))) (by decide)
  have h26 := universalInstance 26 4 (.all 3 (.all 27 pointClause)) (by decide) (by decide) (by decide)
  have ha26 : replace 26 4 (.all 3 (.all 27 pointClause)) =
      .all 3 (.all 27 (replace 26 4 pointClause)) := by decide
  rw [ha26] at h26
  have h3 := allSpecialize 3 (.all 27 (replace 26 4 pointClause)) (by decide)
  have h27 := universalInstance 27 3 (replace 26 4 pointClause) (by decide) (by decide) (by decide)
  simpa only [quantifiedUniqueness,sourcePoint,Formula.encode] using compose h2 (compose h26 (compose h3 h27))

private theorem target_shape : targetPoint = .imp
    (namedBoth (.member 0 2) (namedBoth (.member 0 2) (namedBoth (.member 8 3)
      (namedBoth (.member 8 5) (namedBoth (graphFormula 9 2 3) (graphFormula 9 2 5))))))
    (namedBoth (.imp (.equal 2 2) (.equal 3 5)) (.imp (.equal 3 5) (.equal 2 2))) := by decide
private theorem source_shape : sourcePoint = .imp
    (namedBoth (.member 0 2) (namedBoth (.member 0 4) (namedBoth (.member 8 3)
      (namedBoth (.member 8 3) (namedBoth (graphFormula 9 2 3) (graphFormula 9 4 3))))))
    (namedBoth (.imp (.equal 2 4) (.equal 3 3)) (.imp (.equal 3 3) (.equal 2 4))) := by decide

/-- Every guarded pair of graph9 edges at the same source has equal targets. -/
def target_family_from_uniqueness : KDerivation (imp quantifiedUniqueness.encode targetFamily.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [quantifiedUniqueness.encode]
  have hu : Context Γ quantifiedUniqueness.encode := .head _ _
  have hp : Context Γ targetBody.encode := by
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Δ := [(graphFormula 9 2 5).encode,(graphFormula 9 2 3).encode,member 8 5,member 8 3,member 0 2,
      quantifiedUniqueness.encode]
    have he2 : Context Δ (graphFormula 9 2 5).encode := .head _ _
    have he1 : Context Δ (graphFormula 9 2 3).encode := .hypothesis (by simp [Δ])
    have hm5 : Context Δ (member 8 5) := .hypothesis (by simp [Δ])
    have hm3 : Context Δ (member 8 3) := .hypothesis (by simp [Δ])
    have hm2 : Context Δ (member 0 2) := .hypothesis (by simp [Δ])
    have hu' : Context Δ quantifiedUniqueness.encode := .hypothesis (by simp [Δ])
    have hpoint : Context Δ targetPoint.encode := .mp hu' (.closed target_instance)
    rw [target_shape] at hpoint
    have hguard : Context Δ (both (member 0 2) (both (member 0 2) (both (member 8 3)
      (both (member 8 5) (both (graphFormula 9 2 3).encode (graphFormula 9 2 5).encode))))) :=
      Context.conjunctionIntro hm2 (Context.conjunctionIntro hm2 (Context.conjunctionIntro hm3
        (Context.conjunctionIntro hm5 (Context.conjunctionIntro he1 he2))))
    have hc : Context Δ (both (imp (equal 2 2) (equal 3 5)) (imp (equal 3 5) (equal 2 2))) := .mp hguard hpoint
    have he : Context Δ (equal 3 5) := .mp (.closed (equalityReflexive 2)) (Context.conjunctionLeft hc)
    exact Context.eqSymm he
  have hv (v : Nat) (fresh : v ∉ quantifiedUniqueness.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = quantifiedUniqueness.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity v quantifiedUniqueness fresh
  have hall := Context.generalize 2 (hv 2 (by decide))
    (Context.generalize 3 (hv 3 (by decide)) (Context.generalize 5 (hv 5 (by decide)) hp))
  simpa only [targetFamily,Formula.encode] using hall

/-- Every guarded pair of graph9 edges at the same target has equal sources. -/
def source_family_from_uniqueness : KDerivation (imp quantifiedUniqueness.encode
    PASoundness.PAtoCompactConditionalTransitivitySourceAll.family.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [quantifiedUniqueness.encode]
  have hp : Context Γ PASoundness.PAtoCompactConditionalTransitivitySourceAll.point.encode := by
    apply Context.deduction
    let G := PASoundness.PAtoCompactConditionalTransitivitySourceAll.guard.encode
    let Δ := [G,quantifiedUniqueness.encode]
    have hg : Context Δ G := .head _ _
    have hu : Context Δ quantifiedUniqueness.encode := .hypothesis (by simp [Δ])
    have hm3 : Context Δ (member 8 3) := Context.conjunctionLeft hg
    have hr := Context.conjunctionRight hg
    have hm2 : Context Δ (member 0 2) := Context.conjunctionLeft hr
    have hr := Context.conjunctionRight hr
    have hm4 : Context Δ (member 0 4) := Context.conjunctionLeft hr
    have hr := Context.conjunctionRight hr
    have he1 : Context Δ (graphFormula 9 2 3).encode := Context.conjunctionLeft hr
    have he2 : Context Δ (graphFormula 9 4 3).encode := Context.conjunctionRight hr
    have hpoint : Context Δ sourcePoint.encode := .mp hu (.closed source_instance)
    rw [source_shape] at hpoint
    have hguard : Context Δ (both (member 0 2) (both (member 0 4) (both (member 8 3)
      (both (member 8 3) (both (graphFormula 9 2 3).encode (graphFormula 9 4 3).encode))))) :=
      Context.conjunctionIntro hm2 (Context.conjunctionIntro hm4 (Context.conjunctionIntro hm3
        (Context.conjunctionIntro hm3 (Context.conjunctionIntro he1 he2))))
    have hc : Context Δ (both (imp (equal 2 4) (equal 3 3)) (imp (equal 3 3) (equal 2 4))) := .mp hguard hpoint
    have he : Context Δ (equal 2 4) := .mp (.closed (equalityReflexive 3)) (Context.conjunctionRight hc)
    exact Context.eqSymm he
  have hv (v : Nat) (fresh : v ∉ quantifiedUniqueness.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = quantifiedUniqueness.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity v quantifiedUniqueness fresh
  have hall := Context.generalize 3 (hv 3 (by decide))
    (Context.generalize 2 (hv 2 (by decide)) (Context.generalize 4 (hv 4 (by decide)) hp))
  simpa only [PASoundness.PAtoCompactConditionalTransitivitySourceAll.family,Formula.encode] using hall

end PASoundness.PAtoCompactSeededSpanUniquenessFamilies

#print axioms PASoundness.PAtoCompactSeededSpanUniquenessFamilies.target_family_from_uniqueness
#print axioms PASoundness.PAtoCompactSeededSpanUniquenessFamilies.source_family_from_uniqueness
