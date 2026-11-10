import PASoundness.PAtoCompactProductMatchEquivAlignment
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Fixed-label product-output equivalence under the explicit source-candidate,
product matrices and both factor isomorphism matrices. This does not yet
instantiate arbitrary PA term graphs or discharge their guard assumptions. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchEquivFixed

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactProductMatchCollectionOrderUnique PASoundness.PAtoCompactProductMatchExplicitIsomorphism
open PASoundness.PAtoCompactProductMatchEquivAlignment

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def fixed_product_equivalence : KDerivation
    (imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (equivAt 100 2 44).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,extendedMatrices.encode]
  have hc : Context Γ C := .head _ _
  have hm : Context Γ extendedMatrices.encode := .hypothesis (by simp [Γ])
  have hi := Context.mp hc (Context.mp hm (.closed product_explicit_isomorphism))
  simpa [Γ, C] using Context.mp hi (.closed explicit_to_equivAt)

/-- Rebase the fixed-output quotient instance to any allocator whose private
block is above both named endpoints. -/
def fixed_product_equivalence_at (b : Nat) (h₂ : 2 < b + 2) (h₄₄ : 44 < b + 2) : KDerivation
    (imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (equivAt b 2 44).encode)) := by
  have ha := (equivAt_base_alpha 100 b 2 44 (by decide) (by decide) h₂ h₄₄).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,extendedMatrices.encode]
  have hc : Context Γ C := .head _ _
  have hm : Context Γ extendedMatrices.encode := .hypothesis (by simp [Γ])
  have he := Context.mp hc (Context.mp hm (.closed fixed_product_equivalence))
  simpa [Γ, C] using Context.mp he (.closed ha)

theorem fixed_product_equivalence_certificate : theoremCode (certificate fixed_product_equivalence) =
    imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (equivAt 100 2 44).encode) := certificate_correct _

theorem fixed_product_equivalence_at_certificate (b : Nat) (h₂ : 2 < b + 2) (h₄₄ : 44 < b + 2) :
    theoremCode (certificate (fixed_product_equivalence_at b h₂ h₄₄)) =
      imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
        (equivAt b 2 44).encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchEquivFixed

#print axioms PASoundness.PAtoCompactProductMatchEquivFixed.fixed_product_equivalence
#print axioms PASoundness.PAtoCompactProductMatchEquivFixed.fixed_product_equivalence_at
#print axioms PASoundness.PAtoCompactProductMatchEquivFixed.fixed_product_equivalence_certificate
#print axioms PASoundness.PAtoCompactProductMatchEquivFixed.fixed_product_equivalence_at_certificate
