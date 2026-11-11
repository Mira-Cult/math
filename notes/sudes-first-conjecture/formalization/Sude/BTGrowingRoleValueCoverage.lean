import Sude.BTGrowingOffsetPhysical
import Sude.BTGrowingFootprintCoverage

/-! Exact trace-footprint value coverage of supplied physical growth roles. -/
namespace Sude
noncomputable section

/-- If one square satisfies the indexed growth-role placement and all prefix
pair slots are used, the values at those roles are exactly the union of the
trace's stage footprints. This includes zero stages or zero pairs. -/
theorem bt_growing_role_values_eq_footprints
    {g Q n P d r L : ℕ} {initial final : Finset ℕ} {R last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial R final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (offset : ℕ) (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P * r) (hc : cols.length = P * r)
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : PrefixPhysicalInputs P d r n,
      entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val) :
    (Finset.univ.image (btGrowingOffsetCells offset hoff hs choice rows cols hr hc)).image (entry a) =
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
  classical
  rw [← trace.poolValues_image_eq_footprints hlen hpool]
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, ⟨x, rfl⟩, hv⟩
    exact ⟨prefixPhysicalInput hfit hdiag x, by simpa [hplaced x] using hv⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := (prefixPhysicalInput_bijective (P := P) hfit hdiag hexact).2 y
    exact ⟨_, ⟨x, rfl⟩, by simpa [hplaced x, hx] using hy⟩

end
end Sude
