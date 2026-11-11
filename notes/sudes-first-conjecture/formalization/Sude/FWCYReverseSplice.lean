import Sude.ReferenceCompletionEntryInputs
import Sude.ActiveSupportFullKeepout
import Sude.RFCompletionFreeResidual

/-! Reverse a supplied CY completion over one active support. The original
completion remains the reference; no prime, flow, or numeric gate is inferred. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- A completion fixing the old reference on the full reservation can be
spliced to the ordered square on that reservation. Its free entries and hence
its row and column completion residuals are unchanged. -/
theorem fw_cy_reverse_splice
    {n : ℕ} (ordered oldReference cy : Cell n ≃ Fin (n*n))
    (roles full : Finset (Cell n)) (K : ℝ)
    (hsub : roles ⊆ full)
    (hoff : ∀ z ∉ roles, entry oldReference z = entry ordered z)
    (himage : roles.image (entry oldReference) = roles.image (entry ordered))
    (hcy : ∀ z ∈ full, entry cy z = entry oldReference z)
    (hrow : ∀ r, |(rowSum cy r : ℝ) - ((∑ z ∈ rowCells r ∩ full, (entry oldReference z : ℝ)) +
      ((rowCells r \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| < K)
    (hcol : ∀ c, |(columnSum cy c : ℝ) - ((∑ z ∈ columnCells c ∩ full, (entry oldReference z : ℝ)) +
      ((columnCells c \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| < K) :
    ∃ completed : Cell n ≃ Fin (n*n),
      (∀ z ∈ full, entry completed z = entry ordered z) ∧
      (∀ z ∈ roles, entry cy z = entry oldReference z) ∧
      (∀ z ∉ roles, entry cy z = entry completed z) ∧
      (∀ r, |(rowSum completed r : ℝ) - ((∑ z ∈ rowCells r ∩ full, (entry ordered z : ℝ)) +
        ((rowCells r \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| < K) ∧
      (∀ c, |(columnSum completed c : ℝ) - ((∑ z ∈ columnCells c ∩ full, (entry ordered z : ℝ)) +
        ((columnCells c \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| < K) := by
  classical
  have hactive : ∀ z ∈ roles, cy z = oldReference z := fun z hz =>
    entry_eq_implies_index_eq cy oldReference z (hcy z (hsub hz))
  have hoff' : ∀ z ∉ roles, ordered z = oldReference z := fun z hz =>
    entry_eq_implies_index_eq ordered oldReference z (hoff z hz).symm
  have himage' : roles.image ordered = roles.image oldReference :=
    entry_image_eq_implies_index_image_eq ordered oldReference roles himage.symm
  obtain ⟨completed, ha, ho⟩ :=
    reference_completion_synchronise oldReference ordered cy roles hactive hoff' himage'
  have ha' : ∀ z ∈ roles, entry completed z = entry ordered z := by
    intro z hz
    unfold entry
    rw [ha z hz]
  have ho' : ∀ z ∉ roles, entry completed z = entry cy z := by
    intro z hz
    unfold entry
    rw [ho z hz]
  have hfixed : ∀ z ∈ full, entry completed z = entry ordered z := by
    intro z hz
    by_cases hr : z ∈ roles
    · exact ha' z hr
    · rw [ho' z hr, hcy z hz, hoff z hr]
  have hpool := (full_keepout_value_image_and_unused_eq ordered oldReference roles full hsub hoff himage).2
  have hres (line : Finset (Cell n)) :
      (∑ z ∈ line, (entry completed z : ℝ)) -
        ((∑ z ∈ line ∩ full, (entry ordered z : ℝ)) +
          ((line \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue) =
      (∑ z ∈ line, (entry cy z : ℝ)) -
        ((∑ z ∈ line ∩ full, (entry oldReference z : ℝ)) +
          ((line \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue) := by
    have h₁ := fixed_reservation_free_line_residual ordered completed full line
      (centralEntriesMean (actualUnusedPool ordered full) centralPoolValue) hfixed
    have h₂ := fixed_reservation_free_line_residual oldReference cy full line
      (centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue) hcy
    rw [h₁, h₂, hpool]
    apply Finset.sum_congr rfl
    intro z hz
    have hzfull : z ∉ full := (Finset.mem_sdiff.mp hz).2
    have hzroles : z ∉ roles := fun hr => hzfull (hsub hr)
    rw [ho' z hzroles]
  refine ⟨completed, hfixed, (fun z hz => hcy z (hsub hz)), (fun z hz => (ho' z hz).symm), ?_, ?_⟩
  · intro r
    have h := hres (rowCells r)
    rw [← rowSum_real_cells completed r, ← rowSum_real_cells cy r] at h
    rw [h]
    exact hrow r
  · intro c
    have h := hres (columnCells c)
    rw [← columnSum_real_cells completed c, ← columnSum_real_cells cy c] at h
    rw [h]
    exact hcol c

end
end Sude
