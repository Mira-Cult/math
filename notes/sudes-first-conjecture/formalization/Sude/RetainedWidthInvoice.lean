import Sude.PermutedSeedMidpoints
import Sude.NarrowSeedSorted

/-! Reindex the source's selected-group width invoice to physical stages. -/
namespace Sude
noncomputable section

/-- The canonical stage enumeration visits only selected natural labels. -/
theorem retainedStageIndex_val_mem (r P : ℕ) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (j : Fin P) :
    (retainedSeedStageIndex r P kept hsub hkept j).val ∈ kept := by
  have hcard : (retainedSeedGroups r kept hsub).card = P := by
    rw [retainedSeedGroups_card, hkept]
  apply (mem_retainedSeedGroups r kept hsub _).1
  simpa [retainedSeedStageIndex] using
    Finset.orderEmbOfFin_mem (retainedSeedGroups r kept hsub) hcard j

/-- Summation over physical stages is exactly summation over the selected
source labels, with no repeated or omitted group. -/
theorem retainedStage_sum (r P : ℕ) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (F : ℕ → ℝ) :
    (∑ j : Fin P, F (retainedSeedStageIndex r P kept hsub hkept j).val) =
      ∑ i ∈ kept, F i := by
  classical
  have hcard : (retainedSeedGroups r kept hsub).card = P := by
    rw [retainedSeedGroups_card, hkept]
  have hrange : Set.range (retainedSeedStageIndex r P kept hsub hkept) =
      (retainedSeedGroups r kept hsub : Set (Fin r)) := by
    simpa [retainedSeedStageIndex] using
      Finset.range_orderEmbOfFin (retainedSeedGroups r kept hsub) hcard
  apply Finset.sum_bij (fun j _ => (retainedSeedStageIndex r P kept hsub hkept j).val)
  · intro j _
    exact retainedStageIndex_val_mem r P kept hsub hkept j
  · intro j _ k _ heq
    apply retainedSeedStageIndex_injective r P kept hsub hkept
    exact Fin.ext heq
  · intro i hi
    have hir : i < r := Finset.mem_range.mp (hsub hi)
    let fi : Fin r := ⟨i, hir⟩
    have hfi : fi ∈ retainedSeedGroups r kept hsub :=
      (mem_retainedSeedGroups r kept hsub fi).2 hi
    have hs : fi ∈ Set.range (retainedSeedStageIndex r P kept hsub hkept) := by
      rw [hrange]
      exact hfi
    obtain ⟨j, hj⟩ := hs
    exact ⟨j, Finset.mem_univ _, congrArg Fin.val hj⟩
  · intro j _
    rfl

/-- The squared actual-midpoint widths sum to the source's selected-group
squared widths, including any equal-width labels. -/
theorem retainedStage_midpoint_width_sq_sum (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (hQ : 0 < Q) :
    (∑ j : Fin P,
      (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
       retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2) =
    ∑ i ∈ kept, (sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard (i * Q)) ^ 2 := by
  simp_rw [retainedStageMidpoint_range candidates r P Q gap hcard kept hsub hkept hQ]
  exact retainedStage_sum r P kept hsub hkept (fun i =>
    (sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard (i * Q)) ^ 2)

/-- A maximum selected source width is a valid cap for every actual
retained midpoint-stage width. -/
theorem retainedStage_midpoint_width_sq_le {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hQ : 0 < Q) (z : ℝ)
    (hmax : ∀ i ∈ kept, sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard (i * Q) ≤ z) (j : Fin P) :
    (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
     retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2 ≤ z ^ 2 := by
  have hbetween := (retainedStageMidpoint_bounds candidates r P Q gap hcard kept hsub hkept
    initial hav hQ j ⟨0, hQ⟩).2
  have hnon : 0 ≤ retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
      retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩ := sub_nonneg.mpr hbetween
  have hle : retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
      retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩ ≤ z := by
    rw [retainedStageMidpoint_range candidates r P Q gap hcard kept hsub hkept hQ]
    exact hmax _ (retainedStageIndex_val_mem r P kept hsub hkept j)
  exact (sq_le_sq₀ hnon (hnon.trans hle)).2 hle

end
end Sude
