import PASoundness.PAtoCompactProductMatchAllocatedInputs
import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Guarded fixed-label `mulAt` congruence, with literal factor order and
allocator rebasing. It does not assert arbitrary term-graph functionality. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchAllocatedCongruence

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMulBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactProductMatchCollectionConditional PASoundness.PAtoCompactProductMatchInputWitnesses
open PASoundness.PAtoCompactProductMatchCongruenceFixed PASoundness.PAtoCompactProductMatchAllocatedInputs

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

noncomputable def allocated_product_congruence : KDerivation
    (imp (mulAt 100 0 1 2).encode (imp (mulAt 100 42 43 44).encode
      (imp (equivAt 100 0 42).encode (imp (equivAt 100 1 43).encode
        (imp (candidateCode 2 81 77 78 72 64 73 59 75) (equivAt 100 2 44).encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,(equivAt 100 1 43).encode,(equivAt 100 0 42).encode,
    (mulAt 100 42 43 44).encode,(mulAt 100 0 1 2).encode]
  have hc : Context Γ C := .head _ _
  have he₂ : Context Γ (equivAt 100 1 43).encode := .hypothesis (by simp [Γ])
  have he₁ : Context Γ (equivAt 100 0 42).encode := .hypothesis (by simp [Γ])
  have ht : Context Γ (mulAt 100 42 43 44).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (mulAt 100 0 1 2).encode := .hypothesis (by simp [Γ])
  have hp := Context.mp hs (.closed source_product_input)
  have hq := Context.mp ht (.closed target_product_input)
  have hf₁ := Context.mp he₁ (.closed first_factor_input)
  have hf₂ := Context.mp he₂ (.closed second_factor_input)
  have hc' : Context Γ (candidateFormula 2).encode := by simpa [C, candidate_formula_code] using hc
  have hg : Context Γ baseGuard.encode := by
    have h := Context.conjunctionIntro hc' (Context.conjunctionIntro hq (Context.conjunctionIntro hf₁ hf₂))
    simpa [baseGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  simpa [Γ, C, result] using Context.mp hg (Context.mp hp (.closed fixed_product_congruence))

/-- Rebase all four relation inputs and the output quotient to any common
allocator whose private labels are above the fixed endpoint names. -/
noncomputable def allocated_product_congruence_at (b : Nat) (hb : 44 < b + 2) : KDerivation
    (imp (mulAt b 0 1 2).encode (imp (mulAt b 42 43 44).encode
      (imp (equivAt b 0 42).encode (imp (equivAt b 1 43).encode
        (imp (candidateCode 2 81 77 78 72 64 73 59 75) (equivAt b 2 44).encode))))) := by
  have hs := (mulAt_base_alpha b 100 0 1 2 (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide)).forward
  have ht := (mulAt_base_alpha b 100 42 43 44 (by omega) (by omega) hb
    (by decide) (by decide) (by decide)).forward
  have he₁ := (equivAt_base_alpha b 100 0 42 (by omega) (by omega) (by decide) (by decide)).forward
  have he₂ := (equivAt_base_alpha b 100 1 43 (by omega) (by omega) (by decide) (by decide)).forward
  have hr := (equivAt_base_alpha 100 b 2 44 (by decide) (by decide) (by omega) hb).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,(equivAt b 1 43).encode,(equivAt b 0 42).encode,
    (mulAt b 42 43 44).encode,(mulAt b 0 1 2).encode]
  have hc : Context Γ C := .head _ _
  have h₂ : Context Γ (equivAt b 1 43).encode := .hypothesis (by simp [Γ])
  have h₁ : Context Γ (equivAt b 0 42).encode := .hypothesis (by simp [Γ])
  have hp₂ : Context Γ (mulAt b 42 43 44).encode := .hypothesis (by simp [Γ])
  have hp₁ : Context Γ (mulAt b 0 1 2).encode := .hypothesis (by simp [Γ])
  have h := Context.mp hc (Context.mp (Context.mp h₂ (.closed he₂))
    (Context.mp (Context.mp h₁ (.closed he₁)) (Context.mp (Context.mp hp₂ (.closed ht))
      (Context.mp (Context.mp hp₁ (.closed hs)) (.closed allocated_product_congruence)))))
  simpa [Γ, C] using Context.mp h (.closed hr)

theorem allocated_product_congruence_certificate : theoremCode (certificate allocated_product_congruence) =
    imp (mulAt 100 0 1 2).encode (imp (mulAt 100 42 43 44).encode
      (imp (equivAt 100 0 42).encode (imp (equivAt 100 1 43).encode
        (imp (candidateCode 2 81 77 78 72 64 73 59 75) (equivAt 100 2 44).encode)))) := certificate_correct _

theorem allocated_product_congruence_at_certificate (b : Nat) (hb : 44 < b + 2) :
    theoremCode (certificate (allocated_product_congruence_at b hb)) =
      imp (mulAt b 0 1 2).encode (imp (mulAt b 42 43 44).encode
        (imp (equivAt b 0 42).encode (imp (equivAt b 1 43).encode
          (imp (candidateCode 2 81 77 78 72 64 73 59 75) (equivAt b 2 44).encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchAllocatedCongruence

#print axioms PASoundness.PAtoCompactProductMatchAllocatedCongruence.allocated_product_congruence
#print axioms PASoundness.PAtoCompactProductMatchAllocatedCongruence.allocated_product_congruence_at
#print axioms PASoundness.PAtoCompactProductMatchAllocatedCongruence.allocated_product_congruence_certificate
#print axioms PASoundness.PAtoCompactProductMatchAllocatedCongruence.allocated_product_congruence_at_certificate
