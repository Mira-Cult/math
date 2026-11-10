import PASoundness.PAtoCompactProductMatchReverseGraphCoverage

/-! Universally quantify pointwise reverse coverage of a supplied guarded
product-match graph. The graph, product matrices and factor bijections remain
explicit assumptions. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseGraphAll

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchGraphOrder PASoundness.PAtoCompactProductMatchReverseGraphCoverage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reverseCoverage : Formula := .all 55 (.imp (.member 44 55) (.ex 32 graphResult))

def reverse_graph_all : KDerivation (imp productMatrix.encode (imp firstBijection.encode
    (imp secondBijection.encode (imp targetMatrix.encode (imp actualMatch.encode reverseCoverage.encode))))) := by
  let P := productMatrix.encode
  let B₁ := firstBijection.encode
  let B₂ := secondBijection.encode
  let T := targetMatrix.encode
  let A := actualMatch.encode
  let Γ := [A,T,B₂,B₁,P]
  have ha : Context Γ A := .head _ _
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hb₂ : Context Γ B₂ := .hypothesis (by simp [Γ])
  have hb₁ : Context Γ B₁ := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have h := Context.mp ha (Context.mp ht (Context.mp hb₂
    (Context.mp hb₁ (Context.mp hp (.closed reverse_graph_coverage)))))
  have hv : ∀ f, f ∈ Γ → KDerivation (imp f (allCode 55 f)) := by
    intro f hf
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hf
    by_cases hA : f = A
    · subst f; exact actualMatch.vacuity 55 (by decide)
    · by_cases hT : f = T
      · subst f; exact targetMatrix.vacuity 55 (by decide)
      · by_cases hB₂ : f = B₂
        · subst f; exact secondBijection.vacuity 55 (by decide)
        · by_cases hB₁ : f = B₁
          · subst f; exact firstBijection.vacuity 55 (by decide)
          · have hP : f = P := (((hf.resolve_left hA).resolve_left hT).resolve_left hB₂).resolve_left hB₁
            subst f; exact productMatrix.vacuity 55 (by decide)
  have hall := Context.generalize 55 hv h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, P, B₁, B₂, T, A, reverseCoverage, Formula.encode] using hall

theorem reverse_graph_all_certificate : theoremCode (certificate reverse_graph_all) =
    imp productMatrix.encode (imp firstBijection.encode (imp secondBijection.encode
      (imp targetMatrix.encode (imp actualMatch.encode reverseCoverage.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseGraphAll

#print axioms PASoundness.PAtoCompactProductMatchReverseGraphAll.reverse_graph_all
#print axioms PASoundness.PAtoCompactProductMatchReverseGraphAll.reverse_graph_all_certificate
