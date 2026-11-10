import PASoundness.PAtoCompactSuccLeftTopClosed
import PASoundness.PAtoCompactSuccCongruenceEdgeAlpha

/-! Complete the pointwise top-source case using the separately constructed
K edge-split theorem. Graph, clean-graph, encoded irreflexivity, target
successor, and new-pair formulas remain explicit object-level antecedents. -/
namespace PASoundness.PAtoCompactSuccLeftTopFinal
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccLeftTopCase
open PASoundness.PAtoCompactSuccLeftTopClosed PASoundness.PAtoCompactSuccCongruenceEdgeAlpha

/-- The new top source has a unique target under the supplied exact graph
hypotheses. This is one pointwise bijection case, not a graph construction. -/
def top_case_final : KDerivation (imp cleanGraph (imp sourceIrreflexive
    (imp targetSuccessor (imp newGraph (imp newPair
      (imp (equal 2 0) (existsCode 3 witnessBody.encode))))))) := by
  let C := cleanGraph
  let R := sourceIrreflexive
  let T := targetSuccessor
  let G := newGraph
  let P := newPair
  let E := equal 2 0
  let Γ := [E,P,G,T,R,C]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hs : Context Γ uniformSplit := .mp hp (.mp hg (.closed edge_split_alpha))
  exact .mp he (.mp hp (.mp hg (.mp ht (.mp hs (.mp hr (.mp hc (.closed top_case_closed)))))))

theorem top_case_final_certificate : theoremCode (certificate top_case_final) =
    imp cleanGraph (imp sourceIrreflexive (imp targetSuccessor (imp newGraph (imp newPair
      (imp (equal 2 0) (existsCode 3 witnessBody.encode)))))) :=
  certificate_correct top_case_final

end PASoundness.PAtoCompactSuccLeftTopFinal

#print axioms PASoundness.PAtoCompactSuccLeftTopFinal.top_case_final
#print axioms PASoundness.PAtoCompactSuccLeftTopFinal.top_case_final_certificate
