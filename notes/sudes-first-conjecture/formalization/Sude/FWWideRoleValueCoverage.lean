import Sude.FWWidePhysicalSlots
import Sude.DoublePairEndpointCoverage

/-! Exact value coverage of the supplied wide physical roles. -/
namespace Sude
noncomputable section

/-- On one square, the actual wide-role value image is exactly the endpoint
union of the supplied blocks, provided the indexed placements hold. -/
theorem fw_wide_role_values_eq_batch {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) :
    (Finset.univ.image (fwWidePhysicalCells hwide hs choice rows cols hr hc)).image (entry a) =
      doubleBatchLow blocks ∪ doubleBatchHigh blocks := by
  classical
  rw [← double_pair_sequence_endpoint_image blocks]
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, ⟨x, rfl⟩, hv⟩
    exact ⟨(Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2), by simpa [hplaced x] using hv⟩
  · rintro ⟨⟨i, side⟩, hv⟩
    obtain ⟨x, hx⟩ := (fwWideFlatSlot_bijective n).2 (Fin.cast hlen i, side)
    refine ⟨_, ⟨x, rfl⟩, ?_⟩
    rw [hplaced x, hx]
    simpa using hv

end
end Sude
