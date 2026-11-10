import PASoundness.PAtoCompactIsoTransportWrapper
import PASoundness.PAtoCompactOrderIsoSwap

/-! Fixed-name packaging for conditional symmetry of the exact order-
isomorphism candidate. This module assumes a finite K matrix-transfer proof
and explicitly assumes represented inverse graphs. Neither is constructed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactIsoConditionalWrapper
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoSwap
open PASoundness.PAtoCompactIsoTransportWrapper
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Literal matrix inside the original candidate's graph existential. -/
def forwardMatrix : Formula := (bijectionFormula.imp orderFormula.not).not

/-- The same matrix with the input names interchanged, before renaming graph 6. -/
def reverseMatrix : Formula :=
  replace 8 1 (replace 1 0 (replace 0 8 forwardMatrix))

/-- Reverse matrix with its graph variable moved to the fresh name 7. -/
def reverseMatrix7 : Formula := replace 6 7 reverseMatrix

/-- Every old oriented edge implies the corresponding inverse edge. -/
def inverseForward : Formula := .all 3 (.all 2
  (.imp (graphFormula 6 2 3) (graphFormula 7 3 2)))

/-- Every inverse edge implies the corresponding old oriented edge. -/
def inverseBackward : Formula := .all 3 (.all 4
  (.imp (graphFormula 7 3 4) (graphFormula 6 4 3)))

/-- Explicit, global pointwise graph correspondence. -/
def inverseMatrix : Formula := (inverseForward.imp inverseBackward.not).not

/-- Conditional K symmetry for the exact candidate and exact swapped formula.
The proof argument `step` is an object-level K derivation of matrix reversal
under supplied graph correspondence. The displayed premise says each graph
which witnesses the forward matrix has a represented corresponding inverse;
this module does not prove that premise or the supplied step. -/
def conditional_symmetry
    (step : KDerivation (imp forwardMatrix.encode
      (imp inverseMatrix.encode reverseMatrix7.encode))) :
    KDerivation (imp (allCode 6 (imp forwardMatrix.encode (existsCode 7 inverseMatrix.encode)))
      (imp equivalentFormula.encode reverseEquivalent.encode)) := by
  have ht := transport_exists 6 7 forwardMatrix inverseMatrix reverseMatrix7
    (by decide) (by decide) (by decide) step
  have ha := (CompactNamed.existentialAlpha 6 7 reverseMatrix
    (by decide) (by decide) (by decide)).2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equivalentFormula.encode, allCode 6
    (imp forwardMatrix.encode (existsCode 7 inverseMatrix.encode))]
  have he : Context Γ equivalentFormula.encode := Context.head _ _
  have hi : Context Γ (allCode 6
      (imp forwardMatrix.encode (existsCode 7 inverseMatrix.encode))) := .hypothesis (by simp [Γ])
  have hr : Context Γ (existsCode 7 reverseMatrix7.encode) := .mp he (.mp hi (.closed ht))
  exact .mp hr (.closed ha)

theorem conditional_symmetry_certificate
    (step : KDerivation (imp forwardMatrix.encode
      (imp inverseMatrix.encode reverseMatrix7.encode))) :
    theoremCode (certificate (conditional_symmetry step)) =
      imp (allCode 6 (imp forwardMatrix.encode (existsCode 7 inverseMatrix.encode)))
        (imp equivalentFormula.encode reverseEquivalent.encode) :=
  certificate_correct (conditional_symmetry step)

end PASoundness.PAtoCompactIsoConditionalWrapper

#print axioms PASoundness.PAtoCompactIsoConditionalWrapper.conditional_symmetry
#print axioms PASoundness.PAtoCompactIsoConditionalWrapper.conditional_symmetry_certificate
