import PASoundness.PAtoCompactAlphaMapOne
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactOrderIsomorphism

/-! Capture-safe bound-coordinate preparation of the original isomorphism
matrices, and transport of both finite K implication directions to fixed
outer labels. This module does not prove suffix equivalence or construct a
graph. Syntactic labels are distinct; represented objects may coincide. -/
namespace PASoundness.PAtoCompactSuffixRebaseMatrixAlpha
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTermTranslation
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Move bound order coordinates 2 and 5 out of the later free-name map. -/
def orderAlpha2 : Formula := mapNames (rename 2 102) orderFormula
def orderAlpha : Formula := mapNames (rename 5 105) orderAlpha2

/-- Move the (disjointly bound) bijection coordinate 2 out of the map. -/
def bijectionAlpha : Formula := mapNames (rename 2 102) bijectionFormula

/-- Alpha conversion uses finite K proof equivalence, before any active
source/target/graph name is reassigned. -/
noncomputable def order_prepare : ProofEquiv orderFormula orderAlpha := by
  have h2 := alpha_map_one 2 102 orderFormula (by decide) (by decide) (by decide) (by decide)
  have h5 := alpha_map_one 5 105 orderAlpha2 (by decide) (by decide) (by decide) (by decide)
  exact h2.trans h5

noncomputable def bijection_prepare : ProofEquiv bijectionFormula bijectionAlpha := by
  exact alpha_map_one 2 102 bijectionFormula (by decide) (by decide) (by decide) (by decide)

/-- Fixed source0→32, target1→8, and graph6→60 name replacements.
Bound coordinate names are unchanged by `replace`. -/
def relabel (f : Formula) : Formula := replace 6 60 (replace 1 8 (replace 0 32 f))

/-- Capture-safe transport of both K implications through the three displayed
name substitutions. The original and prepared formulas both expose binder
avoidance explicitly. -/
noncomputable def relabel_proof_pair (a b : Formula) (h : ProofEquiv a b)
    (ha : ∀ n ∈ [0,32,1,8,6,60], n ∉ a.binders)
    (hb : ∀ n ∈ [0,32,1,8,6,60], n ∉ b.binders) :
    KDerivation (imp (relabel a).encode (relabel b).encode) ×
    KDerivation (imp (relabel b).encode (relabel a).encode) := by
  have h0 := replace_implications 0 32 a b (ha 0 (by simp)) (hb 0 (by simp))
    (ha 32 (by simp)) (hb 32 (by simp)) h.forward h.backward
  have h1 := replace_implications 1 8 (replace 0 32 a) (replace 0 32 b)
    (by simpa only [replace_binders] using ha 1 (by simp))
    (by simpa only [replace_binders] using hb 1 (by simp))
    (by simpa only [replace_binders] using ha 8 (by simp))
    (by simpa only [replace_binders] using hb 8 (by simp)) h0.1 h0.2
  have h6 := replace_implications 6 60 (replace 1 8 (replace 0 32 a))
    (replace 1 8 (replace 0 32 b))
    (by simpa only [replace_binders] using ha 6 (by simp))
    (by simpa only [replace_binders] using hb 6 (by simp))
    (by simpa only [replace_binders] using ha 60 (by simp))
    (by simpa only [replace_binders] using hb 60 (by simp)) h1.1 h1.2
  simpa only [relabel] using h6

/-- Both directions between the original order matrix and its bound-prepared
version at the fixed outer/graph labels. -/
noncomputable def order_relabel :
    KDerivation (imp (relabel orderFormula).encode (relabel orderAlpha).encode) ×
    KDerivation (imp (relabel orderAlpha).encode (relabel orderFormula).encode) := by
  apply relabel_proof_pair orderFormula orderAlpha order_prepare
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Both directions between the original bijection matrix and its prepared
version at the same fixed outer/graph labels. -/
noncomputable def bijection_relabel :
    KDerivation (imp (relabel bijectionFormula).encode (relabel bijectionAlpha).encode) ×
    KDerivation (imp (relabel bijectionAlpha).encode (relabel bijectionFormula).encode) := by
  apply relabel_proof_pair bijectionFormula bijectionAlpha bijection_prepare
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end PASoundness.PAtoCompactSuffixRebaseMatrixAlpha

#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.orderAlpha2
#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.orderAlpha
#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.bijectionAlpha
#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.order_prepare
#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.bijection_prepare
#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.relabel
#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.relabel_proof_pair
#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.order_relabel
#print axioms PASoundness.PAtoCompactSuffixRebaseMatrixAlpha.bijection_relabel
