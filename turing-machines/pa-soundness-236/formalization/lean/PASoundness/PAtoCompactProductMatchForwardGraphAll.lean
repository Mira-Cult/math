import PASoundness.PAtoCompactProductMatchForwardGraphCoverage

/-! Universally quantify pointwise forward coverage of a supplied guarded
product-match graph. The graph, product matrices and factor bijections remain
explicit assumptions. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchForwardGraphAll

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchGraphOrder PASoundness.PAtoCompactProductMatchForwardGraphCoverage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def forwardCoverage : Formula := .all 32 (.imp (.member 2 32) (.ex 35 forwardResult))

def forward_graph_all : KDerivation (imp productMatrix.encode (imp firstBijection.encode
    (imp secondBijection.encode (imp targetMatrix.encode (imp actualMatch.encode forwardCoverage.encode))))) := by
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
    (Context.mp hb₁ (Context.mp hp (.closed forward_graph_coverage)))))
  have hv : ∀ f, f ∈ Γ → KDerivation (imp f (allCode 32 f)) := by
    intro f hf
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hf
    by_cases hA : f = A
    · subst f; exact actualMatch.vacuity 32 (by decide)
    · by_cases hT : f = T
      · subst f; exact targetMatrix.vacuity 32 (by decide)
      · by_cases hB₂ : f = B₂
        · subst f; exact secondBijection.vacuity 32 (by decide)
        · by_cases hB₁ : f = B₁
          · subst f; exact firstBijection.vacuity 32 (by decide)
          · have hP : f = P := (((hf.resolve_left hA).resolve_left hT).resolve_left hB₂).resolve_left hB₁
            subst f; exact productMatrix.vacuity 32 (by decide)
  have hall := Context.generalize 32 hv h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  simpa [Γ, P, B₁, B₂, T, A, forwardCoverage, Formula.encode] using hall

theorem forward_graph_all_certificate : theoremCode (certificate forward_graph_all) =
    imp productMatrix.encode (imp firstBijection.encode (imp secondBijection.encode
      (imp targetMatrix.encode (imp actualMatch.encode forwardCoverage.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchForwardGraphAll

#print axioms PASoundness.PAtoCompactProductMatchForwardGraphAll.forward_graph_all
#print axioms PASoundness.PAtoCompactProductMatchForwardGraphAll.forward_graph_all_certificate
