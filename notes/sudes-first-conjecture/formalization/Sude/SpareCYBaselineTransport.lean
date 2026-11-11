import Sude.OffSupportReservationImage
import Sude.CentralPhysicalPlacement
import Sude.Switches

/-! Transport of supplied CY diagonal errors through one cell permutation
confined to the reservation. No CY completion or target prime is constructed. -/
namespace Sude
noncomputable section

/-- The error relative to the reserved part of any finite line is unchanged
when both functions are precomposed by the same reservation permutation and
agree on the reservation. -/
theorem reservation_line_error_perm {α : Type*} [DecidableEq α]
    (line full : Finset α) (σ : Equiv.Perm α) (c a : α → ℝ)
    (hfix : ∀ z ∉ full, σ z = z)
    (hag : ∀ z ∈ full, c z = a z) :
    (∑ z ∈ line, c (σ z)) - (∑ z ∈ line ∩ full, a (σ z)) =
      (∑ z ∈ line, c z) - (∑ z ∈ line ∩ full, a z) := by
  classical
  have himage := off_reservation_perm_image full σ hfix
  have hins : ∀ z ∈ full, σ z ∈ full := by
    intro z hz
    rw [← himage]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hsum : (∑ z ∈ line, (c (σ z) - c z)) =
      ∑ z ∈ line ∩ full, (a (σ z) - a z) := by
    calc
      _ = ∑ z ∈ line ∩ full, (c (σ z) - c z) := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro z hz hnot
        have hout : z ∉ full := fun hf => hnot (Finset.mem_inter.mpr ⟨hz, hf⟩)
        rw [hfix z hout]
        exact sub_self _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z hz
        have hf := (Finset.mem_inter.mp hz).2
        rw [hag (σ z) (hins z hf), hag z hf]
  simp only [Finset.sum_sub_distrib] at hsum
  linarith

/-- The actual unused pool and both supplied diagonal baseline errors survive
the same reservation-confined cell permutation. No distinctness of the two
diagonals or positivity of the bounds is required. -/
theorem supplied_cy_reservation_perm_diagonal_errors {n : ℕ}
    (full : Finset (Cell n)) (σ : Equiv.Perm (Cell n))
    (c a : Cell n ≃ Fin (n*n)) (E₁ E₂ : ℝ)
    (hfix : ∀ z ∉ full, σ z = z)
    (hag : ∀ z ∈ full, entry c z = entry a z)
    (hmain : |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) +
      ((mainCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤ E₁)
    (hanti : |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) +
      ((antiCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤ E₂) :
    actualUnusedPool (σ.trans a) full = actualUnusedPool a full ∧
    |(mainSum (σ.trans c) : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry (σ.trans a) z : ℝ)) +
      ((mainCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool (σ.trans a) full) centralPoolValue)| ≤ E₁ ∧
    |(antiSum (σ.trans c) : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry (σ.trans a) z : ℝ)) +
      ((antiCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool (σ.trans a) full) centralPoolValue)| ≤ E₂ := by
  classical
  have hu := (off_support_reservation_value_images full full (fun _ h => h) σ hfix a).2.2
  have hline (line : Finset (Cell n)) := reservation_line_error_perm line full σ
    (fun z => (entry c z : ℝ)) (fun z => (entry a z : ℝ)) hfix
    (fun z hz => by exact_mod_cast hag z hz)
  have hm (b : Cell n ≃ Fin (n*n)) :
      (∑ z ∈ mainCells n, (entry b z : ℝ)) = (mainSum b : ℝ) := by
    unfold mainCells mainSum
    rw [Finset.sum_image (by intro x _ y _ h; exact congrArg Prod.fst h)]
    simp
  have ha (b : Cell n ≃ Fin (n*n)) :
      (∑ z ∈ antiCells n, (entry b z : ℝ)) = (antiSum b : ℝ) := by
    unfold antiCells antiSum
    rw [Finset.sum_image (by intro x _ y _ h; exact congrArg Prod.fst h)]
    simp
  have h₁ := hline (mainCells n)
  have h₂ := hline (antiCells n)
  change (∑ z ∈ mainCells n, (entry (σ.trans c) z : ℝ)) - _ = _ at h₁
  change (∑ z ∈ antiCells n, (entry (σ.trans c) z : ℝ)) - _ = _ at h₂
  rw [hm, hm] at h₁
  rw [ha, ha] at h₂
  refine ⟨hu, ?_, ?_⟩
  · rw [hu]
    simp only [entry, Equiv.trans_apply] at h₁ hmain ⊢
    convert hmain using 1 <;> congr 1 <;> linarith [h₁]
  · rw [hu]
    simp only [entry, Equiv.trans_apply] at h₂ hanti ⊢
    convert hanti using 1 <;> congr 1 <;> linarith [h₂]

end
end Sude
