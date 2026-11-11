import Sude.ReferenceCompletionEntryInputs

/-! Transfer one already-supplied flow output to a completed square and its
specified synchronized reference. No flow, completion, gate, or prime target
is constructed by this statement. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- Synchronize a supplied original flow output with the same completed square.
The two old outputs must agree with the old ordered square off the active set;
the new reference is fixed explicitly on both the active and inactive parts. -/
theorem flow_output_completion_sync {n : ℕ}
    (a b₀ b c d : Cell n ≃ Fin (n*n)) (active full protectedCells : Finset (Cell n))
    (hactiveFull : active ⊆ full)
    (hcompleted : ∀ z ∈ full, entry c z = entry a z)
    (hreferenceOff : ∀ z ∉ active, entry b₀ z = entry a z)
    (houtputOff : ∀ z ∉ active, entry b z = entry a z)
    (houtputImage : active.image (entry b) = active.image (entry a))
    (hdActive : ∀ z ∈ active, entry d z = entry b₀ z)
    (hdOff : ∀ z ∉ active, entry d z = entry c z)
    (hprotected : ∀ z ∈ protectedCells, entry b z = entry b₀ z)
    (hmain : mainSum b = mainSum b₀) (hanti : antiSum b = antiSum b₀) :
    ∃ b' : Cell n ≃ Fin (n*n),
      (∀ z ∈ active, entry b' z = entry b z) ∧
      (∀ z ∉ active, entry b' z = entry c z) ∧
      (∀ r, (rowSum b' r : ℤ) - (rowSum d r : ℤ) =
        (rowSum b r : ℤ) - (rowSum b₀ r : ℤ)) ∧
      (∀ col, (columnSum b' col : ℤ) - (columnSum d col : ℤ) =
        (columnSum b col : ℤ) - (columnSum b₀ col : ℤ)) ∧
      mainSum b' = mainSum d ∧ antiSum b' = antiSum d ∧
      (∀ z ∈ protectedCells, entry b' z = entry d z) ∧
      active.image (entry b') = active.image (entry b) ∧
      Set.range (entry b') = pool n ∧ Function.Injective (entry b') := by
  classical
  have hca : ∀ z ∈ active, c z = a z := fun z hz =>
    entry_eq_implies_index_eq c a z (hcompleted z (hactiveFull hz))
  have hba : ∀ z ∉ active, b z = a z := fun z hz =>
    entry_eq_implies_index_eq b a z (houtputOff z hz)
  have himage := entry_image_eq_implies_index_image_eq b a active houtputImage
  obtain ⟨b', hba', hco'⟩ := reference_completion_synchronise a b c active hca hba himage
  have hbActive : ∀ z ∈ active, entry b' z = entry b z := by
    intro z hz
    unfold entry
    rw [hba' z hz]
  have hbOff : ∀ z ∉ active, entry b' z = entry c z := by
    intro z hz
    unfold entry
    rw [hco' z hz]
  have hpoint (z : Cell n) : (entry b' z : ℤ) - entry d z =
      (entry b z : ℤ) - entry b₀ z := by
    by_cases hz : z ∈ active
    · rw [hbActive z hz, hdActive z hz]
    · rw [hbOff z hz, hdOff z hz, houtputOff z hz, hreferenceOff z hz]
      simp
  have hrow (r : Fin n) : (rowSum b' r : ℤ) - (rowSum d r : ℤ) =
      (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) := by
    have hh : (∑ i : Fin n, ((entry b' (r,i) : ℤ) - entry d (r,i))) =
        ∑ i : Fin n, ((entry b (r,i) : ℤ) - entry b₀ (r,i)) :=
      Finset.sum_congr rfl (fun i _ => hpoint (r,i))
    simpa only [Finset.sum_sub_distrib, ← Nat.cast_sum, rowSum] using hh
  have hcol (col : Fin n) : (columnSum b' col : ℤ) - (columnSum d col : ℤ) =
      (columnSum b col : ℤ) - (columnSum b₀ col : ℤ) := by
    have hh : (∑ i : Fin n, ((entry b' (i,col) : ℤ) - entry d (i,col))) =
        ∑ i : Fin n, ((entry b (i,col) : ℤ) - entry b₀ (i,col)) :=
      Finset.sum_congr rfl (fun i _ => hpoint (i,col))
    simpa only [Finset.sum_sub_distrib, ← Nat.cast_sum, columnSum] using hh
  have hm : mainSum b' = mainSum d := by
    have hh : (∑ i : Fin n, ((entry b' (i,i) : ℤ) - entry d (i,i))) =
        ∑ i : Fin n, ((entry b (i,i) : ℤ) - entry b₀ (i,i)) :=
      Finset.sum_congr rfl (fun i _ => hpoint (i,i))
    simp only [Finset.sum_sub_distrib, ← Nat.cast_sum] at hh
    change (mainSum b' : ℤ) - (mainSum d : ℤ) =
      (mainSum b : ℤ) - (mainSum b₀ : ℤ) at hh
    have hc : (mainSum b : ℤ) = mainSum b₀ := by exact_mod_cast hmain
    have hh' : (mainSum b' : ℤ) = mainSum d := by omega
    exact_mod_cast hh'
  have ha : antiSum b' = antiSum d := by
    have hh : (∑ i : Fin n, ((entry b' (i,i.rev) : ℤ) - entry d (i,i.rev))) =
        ∑ i : Fin n, ((entry b (i,i.rev) : ℤ) - entry b₀ (i,i.rev)) :=
      Finset.sum_congr rfl (fun i _ => hpoint (i,i.rev))
    simp only [Finset.sum_sub_distrib, ← Nat.cast_sum] at hh
    change (antiSum b' : ℤ) - (antiSum d : ℤ) =
      (antiSum b : ℤ) - (antiSum b₀ : ℤ) at hh
    have hc : (antiSum b : ℤ) = antiSum b₀ := by exact_mod_cast hanti
    have hh' : (antiSum b' : ℤ) = antiSum d := by omega
    exact_mod_cast hh'
  refine ⟨b', hbActive, hbOff, hrow, hcol, hm, ha, ?_, ?_, entry_range b', entry_injective b'⟩
  · intro z hz
    by_cases h : z ∈ active
    · rw [hbActive z h, hdActive z h, hprotected z hz]
    · rw [hbOff z h, hdOff z h]
  · apply Finset.image_congr
    intro z hz
    exact hbActive z hz

end
end Sude
