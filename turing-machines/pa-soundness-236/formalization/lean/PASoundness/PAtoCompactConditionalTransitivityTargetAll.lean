import PASoundness.PAtoCompactConditionalTransitivityTargetComposite
import PASoundness.CompactFreshen

/-! Quantified forward uniqueness for an explicitly supplied restricted
composition graph. This does not assert existence or a bijection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityTargetAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivitySecondUnique
open PASoundness.PAtoCompactConditionalTransitivityTargetComposite
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def background : Formula := namedBoth bijectionFormula (namedBoth secondBijection composition)

def targetBody : Formula := .imp (.member 0 2) (.imp (.member 8 3) (.imp (.member 8 5)
  (.imp (graphFormula 9 2 3) (.imp (graphFormula 9 2 5) (.equal 5 3)))))

/-- Every guarded pair of composite edges from the same source has equal
targets. The order 5=3 matches the candidate's uniqueness clause. -/
def targetFamily : Formula := .all 2 (.all 3 (.all 5 targetBody))

private theorem background_names_lt : ∀ v ∈ background.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ background.names.sup id at hm
  have hb : background.names.sup id < 30 := by decide
  omega

private def freshBackground := freshen background 30 background_names_lt
private theorem fresh_no2 : 2 ∉ freshBackground.formula.names := by decide
private theorem fresh_no3 : 3 ∉ freshBackground.formula.names := by decide
private theorem fresh_no5 : 5 ∉ freshBackground.formula.names := by decide
private def backgroundVacuity (v : Nat) (h : v ∉ freshBackground.formula.names) :
    KDerivation (imp background.encode (allCode v background.encode)) :=
  compose freshBackground.equivalent.forward
    (compose (freshBackground.formula.vacuity v h)
      (allCongr v freshBackground.equivalent.backward))

/-- The quantified family is derived in K from the actual two bijection
clauses and the supplied composition graph condition. -/
def target_family : KDerivation (imp background.encode targetFamily.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [background.encode]
  have h : Context Γ background.encode := Context.head [] _
  have hf : Context Γ bijectionFormula.encode := Context.conjunctionLeft h
  have hg : Context Γ secondBijection.encode := Context.conjunctionLeft (Context.conjunctionRight h)
  have hc : Context Γ composition.encode := Context.conjunctionRight (Context.conjunctionRight h)
  have hlocal : Context Γ targetBody.encode := by
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Δ := [(graphFormula 9 2 5).encode, (graphFormula 9 2 3).encode,
      member 8 5, member 8 3, member 0 2, background.encode]
    have he' : Context Δ (graphFormula 9 2 5).encode := Context.head _ _
    have he : Context Δ (graphFormula 9 2 3).encode := .hypothesis (by simp [Δ])
    have hb' : Context Δ (member 8 5) := .hypothesis (by simp [Δ])
    have hb : Context Δ (member 8 3) := .hypothesis (by simp [Δ])
    have ha : Context Δ (member 0 2) := .hypothesis (by simp [Δ])
    have hf' : Context Δ bijectionFormula.encode := by
      have hh : Context Δ background.encode := .hypothesis (by simp [Δ])
      exact Context.conjunctionLeft hh
    have hg' : Context Δ secondBijection.encode := by
      have hh : Context Δ background.encode := .hypothesis (by simp [Δ])
      exact Context.conjunctionLeft (Context.conjunctionRight hh)
    have hc' : Context Δ composition.encode := by
      have hh : Context Δ background.encode := .hypothesis (by simp [Δ])
      exact Context.conjunctionRight (Context.conjunctionRight hh)
    have hp : Context Δ premises.encode := Context.conjunctionIntro hf'
      (Context.conjunctionIntro hg' (Context.conjunctionIntro hc' (Context.conjunctionIntro ha
        (Context.conjunctionIntro hb (Context.conjunctionIntro hb' (Context.conjunctionIntro he he'))))))
    have heq : Context Δ (equal 3 5) := .mp hp (.closed target_unique_of_composite)
    exact Context.eqSymm heq
  have hv (v : Nat) (hvf : v ∉ freshBackground.formula.names) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro f hf
    have heq : f = background.encode := by simpa [Γ] using hf
    subst f
    exact backgroundVacuity v hvf
  exact Context.generalize 2 (hv 2 fresh_no2) (Context.generalize 3 (hv 3 fresh_no3)
    (Context.generalize 5 (hv 5 fresh_no5) hlocal))

theorem target_family_certificate : theoremCode (certificate target_family) =
    imp background.encode targetFamily.encode := certificate_correct target_family

end PASoundness.PAtoCompactConditionalTransitivityTargetAll

#print axioms PASoundness.PAtoCompactConditionalTransitivityTargetAll.target_family
#print axioms PASoundness.PAtoCompactConditionalTransitivityTargetAll.target_family_certificate
