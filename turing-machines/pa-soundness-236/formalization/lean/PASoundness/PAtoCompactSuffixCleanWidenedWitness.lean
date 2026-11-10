import PASoundness.PAtoCompactSuffixCleanWitness
import PASoundness.PAtoCompactSuffixFilterForwardUpgrade

/-! Preserve one clean suffix isomorphism graph while widening its forward
clause to the containing whole. The relative-complement filter and suffix
equivalence are supplied as explicit object-level antecedents. -/
namespace PASoundness.PAtoCompactSuffixCleanWidenedWitness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactSuffixGuardedForwardUpgrade
open PASoundness.PAtoCompactSuffixFilterForwardUpgrade
open PASoundness.PAtoCompactSuffixCleanGraphGuard PASoundness.PAtoCompactSuffixCleanWitness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixBackward : Formula := .all 3 (.imp (.member 31 3) (.ex 2
  (namedBoth (.member 1 2) (namedBoth (graphFormula 6 2 3)
    (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 4 3)) (.equal 4 2)))))))

def widenedMatrix : Formula := namedBoth cleanMatrix firstClause
def widenedResult : Formula := .ex 6 widenedMatrix

private theorem bijection_code : suffixBijection.encode =
    both suffixForward.encode suffixBackward.encode := by
  have hshape : suffixBijection = namedBoth suffixForward suffixBackward := by decide
  rw [hshape]
  rfl

/-- The same supplied clean graph retains its full suffix isomorphism matrix
and additionally has the exact whole-target forward clause. -/
def widen_clean_matrix : KDerivation (imp suffixFilter.encode
    (imp cleanMatrix.encode widenedMatrix.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [cleanMatrix.encode,suffixFilter.encode]
  have hm : Context Γ cleanMatrix.encode := .head _ _
  have hf : Context Γ suffixFilter.encode := .hypothesis (by simp [Γ])
  have hmatrix := Context.conjunctionLeft hm
  have hclean : Context Γ storedClean.encode := Context.conjunctionRight hm
  have hbij : Context Γ suffixBijection.encode := Context.conjunctionLeft hmatrix
  rw [bijection_code] at hbij
  have hforward : Context Γ suffixForward.encode := Context.conjunctionLeft hbij
  have hguard : Context Γ graphClean.encode := .mp hclean (.closed stored_clean_graph_guard)
  have hwhole : Context Γ firstClause.encode :=
    .mp hguard (.mp hf (.mp hforward (.closed forward_upgrade_from_filter)))
  exact Context.conjunctionIntro hm hwhole

/-- The graph witness is constructed in K from the supplied suffix
equivalence; the same witness satisfies the clean matrix and whole clause. -/
def suffix_clean_widened_witness : KDerivation (imp suffixEquivalence.encode
    (imp suffixFilter.encode widenedResult.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [suffixFilter.encode,suffixEquivalence.encode]
  have hf : Context Γ suffixFilter.encode := .head _ _
  have he : Context Γ suffixEquivalence.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 6 cleanMatrix.encode) := .mp he (.closed suffix_clean_witness)
  have hlocal : Context Γ (imp cleanMatrix.encode widenedResult.encode) := by
    apply Context.deduction
    let Δ := [cleanMatrix.encode,suffixFilter.encode,suffixEquivalence.encode]
    have hm : Context Δ cleanMatrix.encode := .head _ _
    have hwiden : Context Δ widenedMatrix.encode :=
      .mp hm (.mp (.under hf _) (.closed widen_clean_matrix))
    exact .mp hwiden (.closed (existsIntroduce 6 widenedMatrix (by decide)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 6 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases hs : h = suffixFilter.encode
    · subst h; exact free_vacuity 6 suffixFilter (by decide)
    · have he : h = suffixEquivalence.encode := hh.resolve_left hs
      subst h; exact free_vacuity 6 suffixEquivalence (by decide)
  exact Context.existsElim (free_vacuity 6 widenedResult (by decide))
    (Context.generalize 6 hv hlocal) hw

theorem suffix_clean_widened_witness_certificate :
    theoremCode (certificate suffix_clean_widened_witness) =
      imp suffixEquivalence.encode (imp suffixFilter.encode widenedResult.encode) :=
  certificate_correct suffix_clean_widened_witness

end PASoundness.PAtoCompactSuffixCleanWidenedWitness

#print axioms PASoundness.PAtoCompactSuffixCleanWidenedWitness.suffixBackward
#print axioms PASoundness.PAtoCompactSuffixCleanWidenedWitness.widenedMatrix
#print axioms PASoundness.PAtoCompactSuffixCleanWidenedWitness.widenedResult
#print axioms PASoundness.PAtoCompactSuffixCleanWidenedWitness.widen_clean_matrix
#print axioms PASoundness.PAtoCompactSuffixCleanWidenedWitness.suffix_clean_widened_witness
#print axioms PASoundness.PAtoCompactSuffixCleanWidenedWitness.suffix_clean_widened_witness_certificate
