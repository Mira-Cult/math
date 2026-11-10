import PASoundness.PAtoCompactConditionalTransitivityOrderAll

/-! Exact literal target-matrix packaging under an explicitly supplied
bijection-transfer derivation. No graph-existence or full transitivity claim. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityOrderSecond
open PASoundness.PAtoCompactConditionalTransitivityOrderTargetSyntax
open PASoundness.PAtoCompactConditionalTransitivityOrderAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The first matrix is the literal matrix inside the candidate graph
existential. The other two use capture-safe fixed-name replacements. -/
def sourceMatrix : Formula := (bijectionFormula.imp orderFormula.not).not
def secondMatrix : Formula := replace 6 7 (replace 0 1 (replace 1 8 sourceMatrix))
def targetMatrix : Formula := replace 6 9 (replace 1 8 sourceMatrix)

def secondBijection : Formula := replace 6 7 (replace 0 1 (replace 1 8 bijectionFormula))
def targetBijection : Formula := replace 6 9 (replace 1 8 bijectionFormula)

theorem source_matrix_code : sourceMatrix.encode =
    both bijectionFormula.encode orderFormula.encode := rfl
theorem second_matrix_code : secondMatrix.encode =
    both secondBijection.encode secondOrder.encode := rfl
theorem target_matrix_code : targetMatrix.encode =
    both targetBijection.encode targetOrder.encode := rfl

/-- The actual order transfer and a supplied literal K proof of bijection
transfer yield the exact target matrix. The supplied proof and the represented
composition graph remain explicit; neither is obtained in this module. -/
def matrix_of_bijection
    (bijTransfer : KDerivation (imp bijectionFormula.encode
      (imp secondBijection.encode (imp composition.encode targetBijection.encode)))) :
    KDerivation (imp sourceMatrix.encode (imp secondMatrix.encode
      (imp composition.encode targetMatrix.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [composition.encode, secondMatrix.encode, sourceMatrix.encode]
  have hc : Context Γ composition.encode := Context.head _ _
  have hs : Context Γ secondMatrix.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ sourceMatrix.encode := .hypothesis (by simp [Γ])
  have hf' : Context Γ (both bijectionFormula.encode orderFormula.encode) := by
    simpa only [source_matrix_code] using hf
  have hs' : Context Γ (both secondBijection.encode secondOrder.encode) := by
    simpa only [second_matrix_code] using hs
  have hb := Context.conjunctionLeft hf'
  have ho := Context.conjunctionRight hf'
  have hb' := Context.conjunctionLeft hs'
  have ho' := Context.conjunctionRight hs'
  have htargetBij : Context Γ targetBijection.encode :=
    .mp hc (.mp hb' (.mp hb (.closed bijTransfer)))
  have htargetOrder : Context Γ targetOrder.encode :=
    .mp hc (.mp ho' (.mp ho (.closed composite_order)))
  simpa only [target_matrix_code] using Context.conjunctionIntro htargetBij htargetOrder

theorem matrix_of_bijection_certificate
    (bijTransfer : KDerivation (imp bijectionFormula.encode
      (imp secondBijection.encode (imp composition.encode targetBijection.encode)))) :
    theoremCode (certificate (matrix_of_bijection bijTransfer)) =
      imp sourceMatrix.encode (imp secondMatrix.encode
        (imp composition.encode targetMatrix.encode)) :=
  certificate_correct (matrix_of_bijection bijTransfer)

end PASoundness.PAtoCompactConditionalTransitivityMatrix

#print axioms PASoundness.PAtoCompactConditionalTransitivityMatrix.matrix_of_bijection
#print axioms PASoundness.PAtoCompactConditionalTransitivityMatrix.matrix_of_bijection_certificate
