import PASoundness.PAtoCompactConditionalTransitivityForwardClause
import PASoundness.PAtoCompactConditionalTransitivityReverseClause

/-! Exact target-bijection assembly for a supplied restricted composition
graph. This does not construct a graph or assert unconditional transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityBijection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityForwardClause
open PASoundness.PAtoCompactConditionalTransitivityReverseClause
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def secondBijection : Formula := replace 6 7 (replace 0 1 (replace 1 8 bijectionFormula))
def targetBijection : Formula := replace 6 9 (replace 1 8 bijectionFormula)

private theorem target_code : targetBijection.encode = both forwardClause.encode rightClause.encode := by rfl

/-- Actual K proof of the target bijection from the two actual source
bijections and an explicitly supplied guarded composition condition. -/
def bijection_transfer : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode
      (imp composition.encode targetBijection.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [composition.encode, secondBijection.encode, bijectionFormula.encode]
  have hc : Context Γ composition.encode := Context.head _ _
  have hg : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ PAtoCompactConditionalTransitivityTargetAll.background.encode :=
    Context.conjunctionIntro hf (Context.conjunctionIntro hg hc)
  have hl : Context Γ forwardClause.encode := .mp hb (.closed forward_clause)
  have hr : Context Γ rightClause.encode := .mp hb (.closed right_clause)
  rw [target_code]
  exact Context.conjunctionIntro hl hr

theorem bijection_transfer_certificate : theoremCode (certificate bijection_transfer) =
    imp bijectionFormula.encode (imp secondBijection.encode
      (imp composition.encode targetBijection.encode)) := certificate_correct bijection_transfer

end PASoundness.PAtoCompactConditionalTransitivityBijection

#print axioms PASoundness.PAtoCompactConditionalTransitivityBijection.bijection_transfer
#print axioms PASoundness.PAtoCompactConditionalTransitivityBijection.bijection_transfer_certificate
