import PASoundness.PAtoCompactConditionalTransitivityActualUnique
import PASoundness.PAtoCompactConditionalTransitivityPoint
import PASoundness.CompactFreshen

/-! Source uniqueness for two guarded edges of a supplied restricted
composition graph. No composition graph is constructed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivitySourceComposite
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityUniqueness
open PASoundness.PAtoCompactConditionalTransitivitySecondUnique
open PASoundness.PAtoCompactConditionalTransitivityActualUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def secondBody10 : Formula := namedBoth (.member 1 10)
  (namedBoth (graphFormula 6 4 10) (graphFormula 7 10 3))
def secondBody11 : Formula := namedBoth (.member 1 11)
  (namedBoth (graphFormula 6 4 11) (graphFormula 7 11 3))
def secondPath10 : Formula := .ex 10 secondBody10
def secondPath : Formula := .ex 11 secondBody11
def secondEdge : Formula := graphFormula 9 4 3
def secondEndpoints : Formula := namedBoth (.member 0 4) (.member 8 3)

private theorem second_replacement : replace 2 4 point =
    .imp secondEndpoints (namedBoth (.imp secondEdge secondPath10)
      (.imp secondPath10 secondEdge)) := by decide
private theorem body_rename : replace 10 11 secondBody10 = secondBody11 := by decide

/-- The second guarded edge yields a separately named intermediate witness. -/
def second_edge_to_path : KDerivation (imp composition.encode
    (imp (member 0 4) (imp (member 8 3)
      (imp secondEdge.encode secondPath.encode)))) := by
  let point' := (.imp secondEndpoints (namedBoth (.imp secondEdge secondPath10)
    (.imp secondPath10 secondEdge)) : Formula)
  have h2 := universalInstance 2 4 (.all 3 point) (by decide) (by decide) (by decide)
  have h2' : replace 2 4 (.all 3 point) = .all 3 (replace 2 4 point) := by decide
  rw [h2'] at h2
  have h3 := allSpecialize 3 (replace 2 4 point) (by decide)
  rw [second_replacement] at h3
  have hpoint : KDerivation (imp composition.encode point'.encode) := compose h2 h3
  have halpha := (existentialAlpha 10 11 secondBody10 (by decide) (by decide) (by decide)).1
  rw [body_rename] at halpha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondEdge.encode, member 8 3, member 0 4, composition.encode]
  have hc : Context Γ composition.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 4) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have he : Context Γ secondEdge.encode := Context.head _ _
  have hp : Context Γ point'.encode := .mp hc (.closed hpoint)
  have hguard : Context Γ secondEndpoints.encode := Context.conjunctionIntro ha hb
  have hclauses : Context Γ (namedBoth (.imp secondEdge secondPath10)
      (.imp secondPath10 secondEdge)).encode := .mp hguard hp
  have hforward : Context Γ (imp secondEdge.encode secondPath10.encode) :=
    Context.conjunctionLeft hclauses
  have hpath : Context Γ (existsCode 10 secondBody10.encode) := by
    simpa only [secondPath10, Formula.encode] using (.mp he hforward)
  exact .mp hpath (.closed halpha)

/-- Actual two bijection clauses, restricted composition, both source
memberships, the shared target membership, and the two composite edges. -/
def premises : Formula := namedBoth bijectionFormula (namedBoth secondBijection
  (namedBoth composition (namedBoth (.member 0 2) (namedBoth (.member 0 4)
    (namedBoth (.member 8 3) (namedBoth edge secondEdge))))))

def conclusion : Formula := .equal 2 4

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

/-- Under the two actual bijections and supplied guarded composition, two
composite edges ending at the same guarded target have equal sources. -/
def guarded_composite_source_unique : KDerivation (imp premises.encode conclusion.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [premises.encode]
  have h : Context Γ premises.encode := Context.head [] _
  have hf : Context Γ bijectionFormula.encode := Context.conjunctionLeft h
  have htail := Context.conjunctionRight h
  have hg : Context Γ secondBijection.encode := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hc : Context Γ composition.encode := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have ha : Context Γ (member 0 2) := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have ha' : Context Γ (member 0 4) := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hb : Context Γ (member 8 3) := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have he : Context Γ edge.encode := Context.conjunctionLeft htail
  have he' : Context Γ secondEdge.encode := Context.conjunctionRight htail
  have hpath10 : Context Γ (existsCode 10 pathBody.encode) := by
    simpa only [path, Formula.encode] using
      (.mp he (.mp hb (.mp ha (.mp hc (.closed edge_to_path)))))
  have hpath11 : Context Γ (existsCode 11 secondBody11.encode) := by
    simpa only [secondPath, Formula.encode] using
      (.mp he' (.mp hb (.mp ha' (.mp hc (.closed second_edge_to_path)))))
  have hlocal : Context (secondBody11.encode :: pathBody.encode :: Γ) conclusion.encode := by
    let Δ := secondBody11.encode :: pathBody.encode :: Γ
    have hf' : Context Δ bijectionFormula.encode := .under (.under hf _) _
    have hg' : Context Δ secondBijection.encode := .under (.under hg _) _
    have ha1 : Context Δ (member 0 2) := .under (.under ha _) _
    have ha2 : Context Δ (member 0 4) := .under (.under ha' _) _
    have hb1 : Context Δ (member 8 3) := .under (.under hb _) _
    have hp : Context Δ pathBody.encode := .under (Context.head Γ pathBody.encode) _
    have hq : Context Δ secondBody11.encode := Context.head _ _
    have hp10 : Context Δ firstPreimagePath :=
      Context.conjunctionIntro ha1
        (Context.conjunctionIntro (Context.conjunctionLeft hp) (Context.conjunctionRight hp))
    have hp11 : Context Δ secondPreimagePath :=
      Context.conjunctionIntro ha2
        (Context.conjunctionIntro (Context.conjunctionLeft hq) (Context.conjunctionRight hq))
    exact .mp hp11 (.mp hp10 (.mp hb1 (.mp hg' (.mp hf' (.closed source_unique)))))
  have hv11 : ∀ h, h ∈ pathBody.encode :: Γ → KDerivation (imp h (allCode 11 h)) := by
    intro f hf
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hf
    by_cases heq : f = pathBody.encode
    · subst f
      exact pathBody.vacuity 11 (by decide)
    · have heq' : f = premises.encode := hf.resolve_left heq
      subst f
      exact premisesVacuity 11 fresh_no11
  have h11 : Context (pathBody.encode :: Γ) conclusion.encode :=
    Context.existsElim (conclusion.vacuity 11 (by decide))
      (Context.generalize 11 hv11 (Context.deduction hlocal))
      (Context.under hpath11 pathBody.encode)
  have hv10 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 10 h)) := by
    intro f hf
    have heq : f = premises.encode := by simpa [Γ] using hf
    subst f
    exact premisesVacuity 10 fresh_no10
  exact Context.existsElim (conclusion.vacuity 10 (by decide))
    (Context.generalize 10 hv10 (Context.deduction h11)) hpath10

theorem guarded_composite_source_unique_certificate :
    theoremCode (certificate guarded_composite_source_unique) = imp premises.encode conclusion.encode :=
  certificate_correct guarded_composite_source_unique

end PASoundness.PAtoCompactConditionalTransitivitySourceComposite

#print axioms PASoundness.PAtoCompactConditionalTransitivitySourceComposite.guarded_composite_source_unique
#print axioms PASoundness.PAtoCompactConditionalTransitivitySourceComposite.guarded_composite_source_unique_certificate
