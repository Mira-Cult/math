import PASoundness.PAtoCompactProductOutputFixedRelation
import PASoundness.PAtoCompactProductMatchAllocatedInputs

/-! Align the fixed-label output relation transport with allocator-100
mulAt/equivAt syntax. The literal source candidate remains an antecedent;
this is not yet arbitrary-name transport. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputAllocatedFixed

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductOriginalAllocatedAlpha
open PASoundness.PAtoCompactProductMatchAllocatedInputs PASoundness.PAtoCompactProductOutputFixedRelation
open PASoundness.PAtoCompactProductOutputCanonical PASoundness.PAtoCompactCandidateExact

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def targetOriginal : Formula := replace 2 42 (replace 1 44 (replace 0 43 productFormula))
theorem target_original_shape : targetOriginal = targetProduct := by decide

/-- Exact original product/allocated syntax equivalence at factors43,44 and
source output0. -/
noncomputable def source_input : KDerivation (imp (mulAt 100 43 44 0).encode sourceProduct.encode) := by
  let A := productFormula
  let B := mulAt 100 0 1 2
  have ha := original_allocated_alpha 100 (by decide)
  have h0 := replace_implications 0 43 A B (by decide) (by decide) (by decide) (by decide) ha.forward ha.backward
  have h1 := replace_implications 1 44 (replace 0 43 A) (replace 0 43 B)
    (by decide) (by decide) (by decide) (by decide) h0.1 h0.2
  have h2 := replace_implications 2 0 (replace 1 44 (replace 0 43 A)) (replace 1 44 (replace 0 43 B))
    (by decide) (by decide) (by decide) (by decide) h1.1 h1.2
  have hs : replace 2 0 (replace 1 44 (replace 0 43 B)) = mulAt 100 43 44 0 := by decide
  simpa [sourceProduct, A, hs] using h2.2

/-- Exact original product/allocated syntax equivalence at the same factors
and target output42. -/
noncomputable def target_output : KDerivation (imp targetProduct.encode (mulAt 100 43 44 42).encode) := by
  let A := productFormula
  let B := mulAt 100 0 1 2
  have ha := original_allocated_alpha 100 (by decide)
  have h0 := replace_implications 0 43 A B (by decide) (by decide) (by decide) (by decide) ha.forward ha.backward
  have h1 := replace_implications 1 44 (replace 0 43 A) (replace 0 43 B)
    (by decide) (by decide) (by decide) (by decide) h0.1 h0.2
  have h2 := replace_implications 2 42 (replace 1 44 (replace 0 43 A)) (replace 1 44 (replace 0 43 B))
    (by decide) (by decide) (by decide) (by decide) h1.1 h1.2
  have hs : replace 2 42 (replace 1 44 (replace 0 43 B)) = mulAt 100 43 44 42 := by decide
  have h : KDerivation (imp targetOriginal.encode
      (replace 2 42 (replace 1 44 (replace 0 43 B))).encode) := h2.1
  rw [hs, target_original_shape] at h
  exact h

/-- Fixed allocator and names: the actual source multiplication relation,
output equivalence and candidate imply the transported multiplication. -/
noncomputable def allocated_fixed_output : KDerivation
    (imp (mulAt 100 43 44 0).encode (imp (equivAt 100 0 42).encode
      (imp (candidateCode 0 81 77 78 72 64 73 59 75) (mulAt 100 43 44 42).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [candidateCode 0 81 77 78 72 64 73 59 75,(equivAt 100 0 42).encode,(mulAt 100 43 44 0).encode]
  have hc : Context Γ (candidateCode 0 81 77 78 72 64 73 59 75) := .head _ _
  have he : Context Γ (equivAt 100 0 42).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (mulAt 100 43 44 0).encode := .hypothesis (by simp [Γ])
  have hsource := Context.mp hs (.closed source_input)
  have hequiv := Context.mp he (.closed first_factor_input)
  have hc' : Context Γ candidate.encode := by simpa [candidate_code] using hc
  have hout := Context.mp hc' (Context.mp hequiv (Context.mp hsource (.closed fixed_relation_output)))
  exact .mp hout (.closed target_output)

theorem allocated_fixed_output_certificate : theoremCode (certificate allocated_fixed_output) =
    imp (mulAt 100 43 44 0).encode (imp (equivAt 100 0 42).encode
      (imp (candidateCode 0 81 77 78 72 64 73 59 75) (mulAt 100 43 44 42).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputAllocatedFixed

#print axioms PASoundness.PAtoCompactProductOutputAllocatedFixed.source_input
#print axioms PASoundness.PAtoCompactProductOutputAllocatedFixed.target_output
#print axioms PASoundness.PAtoCompactProductOutputAllocatedFixed.allocated_fixed_output
#print axioms PASoundness.PAtoCompactProductOutputAllocatedFixed.allocated_fixed_output_certificate
