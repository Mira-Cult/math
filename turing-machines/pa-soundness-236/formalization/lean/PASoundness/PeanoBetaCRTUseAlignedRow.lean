import PASoundness.PeanoBetaCRTAlignment
import PASoundness.PeanoBetaCRTDependentComponents

/-! Assemble the reviewed aligned row update with two separately supplied
factor/future updates, under one selected condition. Witness selection and the
two remaining component updates are not established here. -/
namespace PASoundness.PeanoBetaCRTUseAlignedRow
open FirstOrder FirstOrder.Language
open Peano
open PeanoBetaCRTInvariant PeanoBetaCRTAlignment

/-- The row component is proved by `rows_component_exact`. The factor and
future components remain explicit PA derivation premises, and all three use
the same selected condition and concrete updated code/product terms. -/
theorem use_aligned_row (φ S : Peano.Formula) (hφ : NamesSafe φ)
    (hFactors : FormulaProves (S.imp ((currentMatrix φ).imp ((rowAssumptions φ).imp
      (FOL.substAt (FOL.substAt nextFactors 11 alignedCode) 12 alignedProduct)))))
    (hFuture : FormulaProves (S.imp ((currentMatrix φ).imp ((rowAssumptions φ).imp
      (FOL.substAt (FOL.substAt nextFuture 11 alignedCode) 12 alignedProduct))))) :
    FormulaProves (S.imp ((currentMatrix φ).imp ((rowAssumptions φ).imp (nextInvariant φ)))) := by
  have h11 : 11 ∉ φ.freeVarFinset := by
    intro h; exact hφ 11 h (by simp [reservedNames])
  have h12 : 12 ∉ φ.freeVarFinset := by
    intro h; exact hφ 12 h (by simp [reservedNames])
  have hb11 : 11 ∉ alignedCode.varFinset := by decide
  have hb12 : 12 ∉ alignedCode.varFinset := by decide
  have hp11 : 11 ∉ alignedProduct.varFinset := by decide
  have hp12 : 12 ∉ alignedProduct.varFinset := by decide
  have hRows : FormulaProves (S.imp ((currentMatrix φ).imp ((rowAssumptions φ).imp
      (FOL.substAt (FOL.substAt (nextRows φ) 11 alignedCode) 12 alignedProduct)))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [rowAssumptions φ, currentMatrix φ, S]
    have hw : FOL.Context Peano.Axiom Γ (rowAssumptions φ) := FOL.Context.head _ _
    have hc : FOL.Context Peano.Axiom Γ (currentMatrix φ) := .hypothesis (by simp [Γ])
    exact .mp (.mp (.closed (rows_component_exact φ hφ)) hw) hc
  exact PeanoBetaCRTDependentComponents.use_selected_components φ S (rowAssumptions φ)
    alignedCode alignedProduct h11 h12 hb11 hb12 hp11 hp12 hRows hFactors hFuture

end PASoundness.PeanoBetaCRTUseAlignedRow
