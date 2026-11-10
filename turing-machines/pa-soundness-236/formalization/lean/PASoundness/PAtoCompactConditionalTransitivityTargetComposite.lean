import PASoundness.PAtoCompactConditionalTransitivityActualUnique
import PASoundness.PAtoCompactConditionalTransitivityPoint
import PASoundness.CompactFreshen

/-! Pointwise target uniqueness for an explicitly supplied restricted
composition graph and the two literal bijection clauses. All endpoint domain
guards remain explicit. No graph construction or full transitivity is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityTargetComposite
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityUniqueness
open PASoundness.PAtoCompactConditionalTransitivitySecondUnique
open PASoundness.PAtoCompactConditionalTransitivityActualUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def secondEdge : Formula := graphFormula 9 2 5
def secondBody10 : Formula := namedBoth (.member 1 10)
  (namedBoth (graphFormula 6 2 10) (graphFormula 7 10 5))
def secondBody11 : Formula := replace 10 11 secondBody10
def secondPath : Formula := .ex 11 secondBody11

private def point5 : Formula := .imp (namedBoth (.member 0 2) (.member 8 5))
  (namedBoth (.imp secondEdge (.ex 10 secondBody10)) (.imp (.ex 10 secondBody10) secondEdge))

private def second_edge_to_path : KDerivation (imp composition.encode
    (imp (member 0 2) (imp (member 8 5) (imp secondEdge.encode secondPath.encode)))) := by
  have h2 := allSpecialize 2 (.all 3 point) (by decide)
  have h3 := universalInstance 3 5 point (by decide) (by decide) (by decide)
  have heq : replace 3 5 point = point5 := by decide
  rw [heq] at h3
  have hpoint : KDerivation (imp composition.encode point5.encode) := compose h2 h3
  have halpha := (existentialAlpha 10 11 secondBody10 (by decide) (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondEdge.encode, member 8 5, member 0 2, composition.encode]
  have he : Context Γ secondEdge.encode := Context.head _ _
  have hc : Context Γ composition.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 2) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 8 5) := .hypothesis (by simp [Γ])
  have hp : Context Γ point5.encode := .mp hc (.closed hpoint)
  have hi : Context Γ (namedBoth (.imp secondEdge (.ex 10 secondBody10))
      (.imp (.ex 10 secondBody10) secondEdge)).encode :=
    .mp (Context.conjunctionIntro ha hb) hp
  have hh : Context Γ (imp secondEdge.encode (existsCode 10 secondBody10.encode)) :=
    Context.conjunctionLeft hi
  have hr : Context Γ (existsCode 10 secondBody10.encode) := .mp he hh
  exact .mp hr (.closed halpha)

/-- Both exact bijection clauses, guarded composition, source and target
memberships, and two edges from the same source. -/
def premises : Formula := namedBoth bijectionFormula (namedBoth secondBijection
  (namedBoth composition (namedBoth (.member 0 2) (namedBoth (.member 8 3)
    (namedBoth (.member 8 5) (namedBoth edge secondEdge))))))

private theorem premises_names_lt : ∀ v ∈ premises.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ premises.names.sup id at hm
  have hb : premises.names.sup id < 30 := by decide
  omega

private def freshPremises := freshen premises 30 premises_names_lt
private theorem fresh_no10 : 10 ∉ freshPremises.formula.names := by decide
private theorem fresh_no11 : 11 ∉ freshPremises.formula.names := by decide
private def premisesVacuity (v : Nat) (h : v ∉ freshPremises.formula.names) :
    KDerivation (imp premises.encode (allCode v premises.encode)) :=
  compose freshPremises.equivalent.forward
    (compose (freshPremises.formula.vacuity v h)
      (allCongr v freshPremises.equivalent.backward))

/-- The target of a supplied composite edge is unique within the displayed
codomain, conditional on the two bijections and guarded graph composition. -/
def target_unique_of_composite : KDerivation (imp premises.encode (equal 3 5)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [premises.encode]
  have h : Context Γ premises.encode := Context.head [] _
  have hf : Context Γ bijectionFormula.encode := Context.conjunctionLeft h
  have ht := Context.conjunctionRight h
  have hg : Context Γ secondBijection.encode := Context.conjunctionLeft ht
  have ht := Context.conjunctionRight ht
  have hc : Context Γ composition.encode := Context.conjunctionLeft ht
  have ht := Context.conjunctionRight ht
  have ha : Context Γ (member 0 2) := Context.conjunctionLeft ht
  have ht := Context.conjunctionRight ht
  have hb : Context Γ (member 8 3) := Context.conjunctionLeft ht
  have ht := Context.conjunctionRight ht
  have hb' : Context Γ (member 8 5) := Context.conjunctionLeft ht
  have ht := Context.conjunctionRight ht
  have he : Context Γ edge.encode := Context.conjunctionLeft ht
  have he' : Context Γ secondEdge.encode := Context.conjunctionRight ht
  have hpath10 : Context Γ (existsCode 10 pathBody.encode) := by
    simpa only [path, Formula.encode] using
      (.mp he (.mp hb (.mp ha (.mp hc (.closed edge_to_path)))))
  have hpath11 : Context Γ (existsCode 11 secondBody11.encode) := by
    simpa only [secondPath, Formula.encode] using
      (.mp he' (.mp hb' (.mp ha (.mp hc (.closed second_edge_to_path)))))
  have hlocal : Context (secondBody11.encode :: pathBody.encode :: Γ) (equal 3 5) := by
    let Δ := secondBody11.encode :: pathBody.encode :: Γ
    have hf' : Context Δ bijectionFormula.encode := .under (.under hf _) _
    have hg' : Context Δ secondBijection.encode := .under (.under hg _) _
    have ha' : Context Δ (member 0 2) := .under (.under ha _) _
    have hb1 : Context Δ (member 8 3) := .under (.under hb _) _
    have hb2 : Context Δ (member 8 5) := .under (.under hb' _) _
    have hp : Context Δ pathBody.encode :=
      Context.under (Context.head Γ pathBody.encode) secondBody11.encode
    have hq : Context Δ secondBody11.encode := Context.head _ _
    have hm : Context Δ (member 1 10) := Context.conjunctionLeft hp
    have hfedge : Context Δ (graphFormula 6 2 10).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hp)
    have hgedge : Context Δ (graphFormula 7 10 3).encode :=
      Context.conjunctionRight (Context.conjunctionRight hp)
    have hm' : Context Δ (member 1 11) := by
      change Context Δ (both (member 1 11) _) at hq
      exact Context.conjunctionLeft hq
    have hfedge' : Context Δ (graphFormula 6 2 11).encode := by
      change Context Δ (both (member 1 11)
        (both (graphFormula 6 2 11).encode (graphFormula 7 11 5).encode)) at hq
      exact Context.conjunctionLeft (Context.conjunctionRight hq)
    have hgedge' : Context Δ (graphFormula 7 11 5).encode := by
      change Context Δ (both (member 1 11)
        (both (graphFormula 6 2 11).encode (graphFormula 7 11 5).encode)) at hq
      exact Context.conjunctionRight (Context.conjunctionRight hq)
    have hp' : Context Δ firstPath := Context.conjunctionIntro hm
      (Context.conjunctionIntro hb1 (Context.conjunctionIntro hfedge hgedge))
    have hq' : Context Δ PAtoCompactConditionalTransitivityUniqueness.secondPath :=
      Context.conjunctionIntro hm' (Context.conjunctionIntro hb2
        (Context.conjunctionIntro hfedge' hgedge'))
    exact .mp hq' (.mp hp' (.mp ha' (.mp hg' (.mp hf' (.closed target_unique)))))
  let C : Formula := .equal 3 5
  have hv11 : ∀ h, h ∈ pathBody.encode :: Γ → KDerivation (imp h (allCode 11 h)) := by
    intro f hf
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hf
    by_cases heq : f = pathBody.encode
    · subst f
      exact pathBody.vacuity 11 (by decide)
    · have heq' : f = premises.encode := hf.resolve_left heq
      subst f
      exact premisesVacuity 11 fresh_no11
  have h11 : Context (pathBody.encode :: Γ) C.encode :=
    Context.existsElim (C.vacuity 11 (by decide))
      (Context.generalize 11 hv11 (Context.deduction hlocal))
      (Context.under hpath11 pathBody.encode)
  have hv10 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 10 h)) := by
    intro f hf
    have heq : f = premises.encode := by simpa [Γ] using hf
    subst f
    exact premisesVacuity 10 fresh_no10
  exact Context.existsElim (C.vacuity 10 (by decide))
    (Context.generalize 10 hv10 (Context.deduction h11)) hpath10

theorem target_unique_of_composite_certificate :
    theoremCode (certificate target_unique_of_composite) = imp premises.encode (equal 3 5) :=
  certificate_correct target_unique_of_composite

end PASoundness.PAtoCompactConditionalTransitivityTargetComposite

#print axioms PASoundness.PAtoCompactConditionalTransitivityTargetComposite.target_unique_of_composite
#print axioms PASoundness.PAtoCompactConditionalTransitivityTargetComposite.target_unique_of_composite_certificate
