import PASoundness.PAtoCompactOrderedPair

/-! An explicit represented diagonal graph for standard HF objects. The
finite set assembly here is a semantic construction, not a K derivation or a
quotient interpretation. -/
namespace PASoundness.PAtoCompactDiagonalGraph
open PASoundness.HFCoding PASoundness.PAtoCompactOrderedPair

/-- The graph containing the canonical pair (a,a) for each member a of x. -/
def diagonalGraph (x : Object) : Object :=
  assemble ((elements x).image (fun a => orderedPair a a))

/-- A diagonal graph contains exactly its indicated canonical pairs. -/
theorem diagonal_membership (x a b : Object) :
    orderedPair a b ∈ diagonalGraph x ↔ a ∈ x ∧ a = b := by
  classical
  simp only [diagonalGraph, mem_assemble, Finset.mem_image, mem_elements]
  constructor
  · rintro ⟨u,hu,he⟩
    obtain ⟨ha,hb⟩ := orderedPair_diag_unique u a b he
    exact ⟨ha ▸ hu, ha.symm.trans hb⟩
  · rintro ⟨ha,rfl⟩
    exact ⟨a,ha,rfl⟩

end PASoundness.PAtoCompactDiagonalGraph

#print axioms PASoundness.PAtoCompactDiagonalGraph.diagonal_membership
