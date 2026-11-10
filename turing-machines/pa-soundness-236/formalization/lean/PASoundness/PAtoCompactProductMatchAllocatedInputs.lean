import PASoundness.PAtoCompactProductMatchCongruenceFixed
import PASoundness.PAtoCompactProductOriginalAllocatedAlpha
import PASoundness.PAtoCompactUnaryGraphFunctional
import PASoundness.PAtoCompactScopedActiveReplace

/-! Align fixed-label product and factor-equivalence inputs with allocator-100
`mulAt` and `equivAt` formulas. This is K alpha transport, not term-graph
functionality or discharge of the source-candidate guard. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchAllocatedInputs

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactProductOriginalAllocatedAlpha
open PASoundness.PAtoCompactUnaryGraphFunctional PASoundness.PAtoCompactEquivNoShadow
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactProductMatchInputWitnesses

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

noncomputable def source_product_input : KDerivation
    (imp (mulAt 100 0 1 2).encode productFormula.encode) :=
  (original_allocated_alpha 100 (by decide)).backward

noncomputable def target_product_input : KDerivation
    (imp (mulAt 100 42 43 44).encode targetProduct.encode) := by
  let A := productFormula
  let B := mulAt 100 0 1 2
  have ha := original_allocated_alpha 100 (by decide)
  have h0 := replace_implications 0 42 A B (by decide) (by decide) (by decide) (by decide) ha.forward ha.backward
  have h1 := replace_implications 1 43 (replace 0 42 A) (replace 0 42 B)
    (by decide) (by decide) (by decide) (by decide) h0.1 h0.2
  have h2 := replace_implications 2 44 (replace 1 43 (replace 0 42 A)) (replace 1 43 (replace 0 42 B))
    (by decide) (by decide) (by decide) (by decide) h1.1 h1.2
  have hs : replace 2 44 (replace 1 43 (replace 0 42 B)) = mulAt 100 42 43 44 := by decide
  simpa [targetProduct, A, hs] using h2.2

private noncomputable def equiv_forward : KDerivation
    (imp equivalentFormula.encode (equivAt 100 0 1).encode) := by
  simpa [equivTemplate, normalizeBottom_encode] using (canonical_equiv_alpha 100 (by decide)).forward
private noncomputable def equiv_backward : KDerivation
    (imp (equivAt 100 0 1).encode equivalentFormula.encode) := by
  simpa [equivTemplate, normalizeBottom_encode] using (canonical_equiv_alpha 100 (by decide)).backward

noncomputable def first_factor_input : KDerivation
    (imp (equivAt 100 0 42).encode firstEquivalent.encode) := by
  let A := equivalentFormula
  let B := equivAt 100 0 1
  have h := replace_implications 1 42 A B (by decide) (by decide) (by decide) (by decide)
    equiv_forward equiv_backward
  have hs : replace 1 42 B = equivAt 100 0 42 := by decide
  simpa [firstEquivalent, A, hs] using h.2

noncomputable def second_factor_input : KDerivation
    (imp (equivAt 100 1 43).encode secondEquivalent.encode) := by
  let A := equivalentFormula
  let B := equivAt 100 0 1
  have h1 := replace_implications 1 43 A B (by decide) (by decide) (by decide) (by decide)
    equiv_forward equiv_backward
  have h0 := replace_implications 0 1 (replace 1 43 A) (replace 1 43 B)
    (by decide) (by decide) (by decide) (by decide) h1.1 h1.2
  have hs : replace 0 1 (replace 1 43 B) = equivAt 100 1 43 := by decide
  simpa [secondEquivalent, A, hs] using h0.2

theorem source_product_input_certificate : theoremCode (certificate source_product_input) =
    imp (mulAt 100 0 1 2).encode productFormula.encode := certificate_correct _
theorem target_product_input_certificate : theoremCode (certificate target_product_input) =
    imp (mulAt 100 42 43 44).encode targetProduct.encode := certificate_correct _
theorem first_factor_input_certificate : theoremCode (certificate first_factor_input) =
    imp (equivAt 100 0 42).encode firstEquivalent.encode := certificate_correct _
theorem second_factor_input_certificate : theoremCode (certificate second_factor_input) =
    imp (equivAt 100 1 43).encode secondEquivalent.encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchAllocatedInputs

#print axioms PASoundness.PAtoCompactProductMatchAllocatedInputs.source_product_input
#print axioms PASoundness.PAtoCompactProductMatchAllocatedInputs.target_product_input
#print axioms PASoundness.PAtoCompactProductMatchAllocatedInputs.first_factor_input
#print axioms PASoundness.PAtoCompactProductMatchAllocatedInputs.second_factor_input
#print axioms PASoundness.PAtoCompactProductMatchAllocatedInputs.source_product_input_certificate
#print axioms PASoundness.PAtoCompactProductMatchAllocatedInputs.target_product_input_certificate
#print axioms PASoundness.PAtoCompactProductMatchAllocatedInputs.first_factor_input_certificate
#print axioms PASoundness.PAtoCompactProductMatchAllocatedInputs.second_factor_input_certificate
