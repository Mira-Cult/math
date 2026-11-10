import PASoundness.PAtoCompactSuffixGraphForwardAll
import PASoundness.PAtoCompactSuffixGraphReverseAll
import PASoundness.PAtoCompactSuffixGraphOrder

/-! Assemble the forward, reverse and order clauses for the SAME supplied
suffix graph. This does not yet construct that graph, identify the matrix with
a canonical isomorphism, or prove addition output transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuffixBoundaryPoint
open PASoundness.PAtoCompactSuffixGraphForwardCoverage
open PASoundness.PAtoCompactSuffixGraphForwardAll
open PASoundness.PAtoCompactSuffixGraphReverseCoverage
open PASoundness.PAtoCompactSuffixGraphReverseAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The forward clause on source suffix40 and target suffix41. -/
def suffixForward : Nat := allCode 7
  (imp (member 40 7) (existsCode 3 suffixForwardWitness.encode))
/-- The reverse clause for the same suffixes and the same graph8. -/
def suffixReverse : Nat := allCode 3
  (imp (member 41 3) (existsCode 7 suffixReverseWitness.encode))
/-- Full displayed matrix, still attached to the supplied graph8. -/
def suffixMatrix : Nat := both (both suffixForward suffixReverse)
  PAtoCompactSuffixGraphOrder.suffixOrder

/-- Under the supplied original isomorphism matrices, selected cut edge,
proper-cut memberships, both exact suffix filters and the endpoint-filtered
restriction of the same original graph6, K derives all three clauses for
that same graph8. Syntactic labels do not require distinct object values. -/
def suffix_graph_matrix : KDerivation
    (imp orderFormula.encode (imp sourceFilter (imp targetFilter
      (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
        (imp bijectionFormula.encode (imp graphFilter suffixMatrix)))))))) := by
  let O := orderFormula.encode
  let S := sourceFilter
  let T := targetFilter
  let C := member 0 2
  let D := member 1 5
  let E := (graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let F := graphFilter
  let Γ := [F,B,E,D,C,T,S,O]
  have hf : Context Γ F := .head _ _
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hforward : Context Γ suffixForward :=
    .mp hf (.mp hb (.mp he (.mp hd (.mp hc (.mp ht (.mp hs
      (.mp ho (.closed suffix_forward_all))))))))
  have hreverse : Context Γ suffixReverse :=
    .mp he (.mp hd (.mp hc (.mp hf (.mp ht (.mp hs (.mp hb
      (.mp ho (.closed suffix_reverse_all))))))))
  have horder : Context Γ PAtoCompactSuffixGraphOrder.suffixOrder :=
    .mp hf (.mp ho (.mp ht (.mp hs (.closed PAtoCompactSuffixGraphOrder.suffix_graph_order))))
  have hresult : Context Γ suffixMatrix :=
    Context.conjunctionIntro (Context.conjunctionIntro hforward hreverse) horder
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hresult

theorem suffix_graph_matrix_certificate : theoremCode (certificate suffix_graph_matrix) =
    imp orderFormula.encode (imp sourceFilter (imp targetFilter
      (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
        (imp bijectionFormula.encode (imp graphFilter suffixMatrix))))))) :=
  certificate_correct suffix_graph_matrix

end PASoundness.PAtoCompactSuffixGraphMatrix

#print axioms PASoundness.PAtoCompactSuffixGraphMatrix.suffixForward
#print axioms PASoundness.PAtoCompactSuffixGraphMatrix.suffixReverse
#print axioms PASoundness.PAtoCompactSuffixGraphMatrix.suffixMatrix
#print axioms PASoundness.PAtoCompactSuffixGraphMatrix.suffix_graph_matrix
#print axioms PASoundness.PAtoCompactSuffixGraphMatrix.suffix_graph_matrix_certificate
