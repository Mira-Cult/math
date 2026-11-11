import Sude.FWSeedMidpointPartition

/-! Exact matched physical-network cancellation for variable pair gaps.
No concentration or full-line estimate is asserted. -/
namespace Sude
noncomputable section

/-- Each supplied matched network slot cancels the orientation contribution
with that pair's own actual gap. The selected-label map is injective on the
selected network slots, so the final sum uses each physical pair label once. -/
theorem physical_network_matched_variable_gap_delta_sum {n : ℕ} {α K : Type*}
    [DecidableEq α] [DecidableEq K] {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs K a) (cells : α × Bool → Cell n)
    (T : Finset K) (ι : K → α) (hinj : Set.InjOn ι (↑T : Set K))
    (r : Fin n) (gap : α → ℝ)
    (hmatch : ∀ k ∈ T, cells (ι k, false) = (v.low k, v.column k) ∧
      cells (ι k, true) = (v.high k, v.column k))
    (hgap : ∀ k ∈ T, (entry a (cells (ι k, true)) : ℝ) -
      entry a (cells (ι k, false)) = gap (ι k)) :
    (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) =
      -(∑ i ∈ T.image ι, gap i * physicalPairLineOrientation cells (fun c => c.1 = r) i) := by
  classical
  calc
    _ = ∑ k ∈ T, -(gap (ι k) * physicalPairLineOrientation cells (fun c => c.1 = r) (ι k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have h := physical_network_matched_pair_delta v cells (ι k) k r (gap (ι k))
        (hmatch k hk).1 (hmatch k hk).2 (hgap k hk)
      simpa only [neg_mul] using h
    _ = -(∑ i ∈ T.image ι, gap i * physicalPairLineOrientation cells (fun c => c.1 = r) i) := by
      rw [Finset.sum_image (by intro x hx y hy h; exact hinj hx hy h)]
      simp only [Finset.sum_neg_distrib]

end
end Sude
