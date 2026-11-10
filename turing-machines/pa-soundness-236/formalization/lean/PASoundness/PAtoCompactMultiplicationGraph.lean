import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactOrderedPairInjectivity
import Mathlib.Data.Finset.Prod

/-! An explicit standard-HF finite graph for the proposed lexicographic
product. This is semantic finite assembly, not a K derivation or a proof that
K can collect this graph. -/
namespace PASoundness.PAtoCompactMultiplicationGraph
open PASoundness.CompactMatrix PASoundness.HFCoding
open PASoundness.PAtoCompactOrderedPair PASoundness.PAtoCompactOrderedPairInjectivity
open PASoundness.PAtoCompactGraphMeaning PASoundness.PAtoCompactMultiplicationCandidate

def productGraph (m n : Nat) : Object :=
  assemble (((Finset.range m).product (Finset.range n)).image fun ij =>
    orderedPair (orderedPair (ordinal ij.1) (ordinal ij.2)) (ordinal (ij.1*n+ij.2)))

/-- The graph contains precisely the standard ordinal product edges. -/
theorem product_graph_edge (m n a b c : Nat) :
    tripleRel (productGraph m n).code a b c ↔
      ∃ i < m, ∃ j < n, a = (ordinal i).code ∧ b = (ordinal j).code ∧
        c = (ordinal (i*n+j)).code := by
  classical
  change orderedPair (orderedPair ⟨a⟩ ⟨b⟩) ⟨c⟩ ∈ productGraph m n ↔ _
  simp only [productGraph, mem_assemble, Finset.mem_image, Prod.exists]
  constructor
  · rintro ⟨i,j, hmem, he⟩
    have ⟨hi,hj⟩ : i < m ∧ j < n := by simpa using hmem
    obtain ⟨hab,hc⟩ := orderedPair_injective
      (orderedPair (ordinal i) (ordinal j)) (ordinal (i*n+j))
      (orderedPair ⟨a⟩ ⟨b⟩) ⟨c⟩ he
    obtain ⟨ha,hb⟩ := orderedPair_injective (ordinal i) (ordinal j) ⟨a⟩ ⟨b⟩ hab
    exact ⟨i,hi,j,hj,(congrArg Object.code ha).symm,
      (congrArg Object.code hb).symm,(congrArg Object.code hc).symm⟩
  · rintro ⟨i,hi,j,hj,ha,hb,hc⟩
    refine ⟨i,j,by simpa using And.intro hi hj,?_⟩
    have ha' : ordinal i = (⟨a⟩ : Object) := code_injective ha.symm
    have hb' : ordinal j = (⟨b⟩ : Object) := code_injective hb.symm
    have hc' : ordinal (i*n+j) = (⟨c⟩ : Object) := code_injective hc.symm
    simp [ha',hb',hc']

end PASoundness.PAtoCompactMultiplicationGraph

#print axioms PASoundness.PAtoCompactMultiplicationGraph.product_graph_edge
