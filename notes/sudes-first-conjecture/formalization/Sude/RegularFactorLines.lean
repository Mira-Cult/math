import Sude.RegularFactorBalance

/-! Identify the matching slots with the actual free row and column cells. -/
namespace Sude
noncomputable section

theorem regularFactor_row_cells {n : ℕ} {E reserved : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (hdec : RegularMatchingDecomposition E ps)
    (hfree : E = Finset.univ \ reserved) (r : Fin n) :
    (Finset.univ : Finset (Fin ps.length)).image (fun j => (r, (ps.get j) r)) =
      rowCells r \ reserved := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    have hm := regularMatchingSlot_mem hdec (j, r)
    rw [hfree] at hm
    exact Finset.mem_sdiff.mpr ⟨by simp, (Finset.mem_sdiff.mp hm).2⟩
  · intro hz
    have hzE : z ∈ E := by
      rw [hfree]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hz).2⟩
    obtain ⟨⟨j, i⟩, heq⟩ := regularMatchingSlot_surjective hdec z hzE
    have hrow : z.1 = r := (mem_rowCells r z).1 (Finset.mem_sdiff.mp hz).1
    have hir : i = r := (congrArg Prod.fst heq).trans hrow
    subst i
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq⟩

theorem regularFactor_column_cells {n : ℕ} {E reserved : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (hdec : RegularMatchingDecomposition E ps)
    (hfree : E = Finset.univ \ reserved) (c : Fin n) :
    (Finset.univ : Finset (Fin ps.length)).image (fun j => ((ps.get j).symm c, c)) =
      columnCells c \ reserved := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    have hm := regularMatchingSlot_mem hdec (j, (ps.get j).symm c)
    have hm' : ((ps.get j).symm c, c) ∈ E := by simpa [regularMatchingSlot] using hm
    rw [hfree] at hm'
    exact Finset.mem_sdiff.mpr ⟨by simp, (Finset.mem_sdiff.mp hm').2⟩
  · intro hz
    have hzE : z ∈ E := by
      rw [hfree]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hz).2⟩
    obtain ⟨⟨j, i⟩, heq⟩ := regularMatchingSlot_surjective hdec z hzE
    have hcol : z.2 = c := (mem_columnCells c z).1 (Finset.mem_sdiff.mp hz).1
    have hic : (ps.get j) i = c := (congrArg Prod.snd heq).trans hcol
    have hi : i = (ps.get j).symm c := by
      apply (ps.get j).injective
      simpa using hic
    subst i
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    simpa [regularMatchingSlot] using heq

theorem regularFactor_row_sum {n : ℕ} {E reserved : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (hdec : RegularMatchingDecomposition E ps)
    (hfree : E = Finset.univ \ reserved) (b : Cell n ≃ Fin (n * n)) (r : Fin n) :
    (∑ z ∈ rowCells r \ reserved, (entry b z : ℝ)) =
      ∑ j : Fin ps.length, (entry b (r, (ps.get j) r) : ℝ) := by
  classical
  rw [← regularFactor_row_cells hdec hfree r]
  rw [Finset.sum_image (by
    intro j _ k _ h
    have he : regularMatchingSlot ps (j, r) = regularMatchingSlot ps (k, r) := h
    exact congrArg Prod.fst (regularMatchingSlot_injective hdec.pairwise_disjoint he))]

theorem regularFactor_column_sum {n : ℕ} {E reserved : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (hdec : RegularMatchingDecomposition E ps)
    (hfree : E = Finset.univ \ reserved) (b : Cell n ≃ Fin (n * n)) (c : Fin n) :
    (∑ z ∈ columnCells c \ reserved, (entry b z : ℝ)) =
      ∑ j : Fin ps.length, (entry b ((ps.get j).symm c, c) : ℝ) := by
  classical
  rw [← regularFactor_column_cells hdec hfree c]
  rw [Finset.sum_image (by
    intro j _ k _ h
    have he : regularMatchingSlot ps (j, (ps.get j).symm c) =
        regularMatchingSlot ps (k, (ps.get k).symm c) := by
      simpa [regularMatchingSlot] using h
    exact congrArg Prod.fst (regularMatchingSlot_injective hdec.pairwise_disjoint he))]

theorem rowSum_real_cells {n : ℕ} (a : Cell n ≃ Fin (n * n)) (r : Fin n) :
    (rowSum a r : ℝ) = ∑ z ∈ rowCells r, (entry a z : ℝ) := by
  classical
  unfold rowCells rowSum
  rw [Finset.sum_image (by intro i hi j hj h; exact congrArg Prod.snd h)]
  simp

theorem columnSum_real_cells {n : ℕ} (a : Cell n ≃ Fin (n * n)) (c : Fin n) :
    (columnSum a c : ℝ) = ∑ z ∈ columnCells c, (entry a z : ℝ) := by
  classical
  unfold columnCells columnSum
  rw [Finset.sum_image (by intro i hi j hj h; exact congrArg Prod.fst h)]
  simp

end
end Sude
