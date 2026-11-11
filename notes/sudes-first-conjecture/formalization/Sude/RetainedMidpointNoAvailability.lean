import Sude.RetainedWidthInvoice

/-! Retained midpoint bounds without any pool-availability hypothesis. -/
namespace Sude
noncomputable section

/-- Sorted retained midpoint bounds require no pool-availability assumption. -/
theorem retainedStageMidpoint_bounds_no_availability
    (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (hQ : 0 < Q) (j : Fin P) (i : Fin Q) :
    retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j i ∈
      Set.Icc (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩)
        (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩) := by
  let group := retainedSeedStageIndex r P kept hsub hkept j
  change sortedSeedMidpoint candidates r Q gap hcard group ⟨0, hQ⟩ ≤
      sortedSeedMidpoint candidates r Q gap hcard group i ∧
    sortedSeedMidpoint candidates r Q gap hcard group i ≤
      sortedSeedMidpoint candidates r Q gap hcard group ⟨Q - 1, by omega⟩
  rw [sortedSeedMidpoint_slot, sortedSeedMidpoint_slot, sortedSeedMidpoint_slot]
  have htop : group.val * Q + (Q - 1) < r * Q := by
    have h := (finProdFinEquiv (group, (⟨Q - 1, by omega⟩ : Fin Q))).isLt
    simp only [finProdFinEquiv] at h
    simpa [Nat.mul_comm, Nat.add_comm] using h
  have hbot := sortedSeedReal_mono candidates r Q hcard
    (group.val * Q + 0) (group.val * Q + i.val) (by omega) (by omega)
  have hhigh := sortedSeedReal_mono candidates r Q hcard
    (group.val * Q + i.val) (group.val * Q + (Q - 1)) (by omega) htop
  exact ⟨by linarith, by linarith⟩

/-- A supplied maximum selected source width caps the squared midpoint widths;
no availability or reserved-set avoidance assumption is needed. -/
theorem retainedStage_midpoint_width_sq_le_no_availability
    (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (hQ : 0 < Q) (z : ℝ)
    (hmax : ∀ i ∈ kept, sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard (i * Q) ≤ z) (j : Fin P) :
    (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
     retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2 ≤ z ^ 2 := by
  have hbetween := (retainedStageMidpoint_bounds_no_availability
    candidates r P Q gap hcard kept hsub hkept hQ j ⟨0, hQ⟩).2
  have hnon : 0 ≤ retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
      retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩ := sub_nonneg.mpr hbetween
  have hle : retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
      retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩ ≤ z := by
    rw [retainedStageMidpoint_range candidates r P Q gap hcard kept hsub hkept hQ]
    exact hmax _ (retainedStageIndex_val_mem r P kept hsub hkept j)
  exact (sq_le_sq₀ hnon (hnon.trans hle)).2 hle

/-- A source selected-group variance invoice is exactly the corresponding
retained-stage width invoice. -/
theorem retainedStage_source_width_budget_no_availability
    (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (hQ : 0 < Q) (d z B : ℝ)
    (hsource : 3 * d * (∑ i ∈ kept,
      (sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
       sortedSeedReal candidates r Q hcard (i * Q)) ^ 2) + 4 * z ^ 2 ≤ B) :
    3 * d * (∑ j : Fin P,
      (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
       retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2) + 4 * z ^ 2 ≤ B := by
  rw [retainedStage_midpoint_width_sq_sum candidates r P Q gap hcard kept hsub hkept hQ]
  exact hsource

end
end Sude
