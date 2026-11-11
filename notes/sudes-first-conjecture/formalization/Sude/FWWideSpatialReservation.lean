import Sude.FWPhysicalExactReservations

/-! FW wide installation with separate physical exclusions and protected
values. Reserving a location from new placement does not by itself preserve
its old entry; that stronger conclusion needs its value charged to deletion. -/
namespace Sude
noncomputable section

/-- The prescribed FW wide supply may be installed into supplied cells
outside an arbitrary spatial exclusion, while the supplied prior cells whose
values were actually protected are preserved. This does not say the old
entries of other excluded cells remain fixed. -/
theorem fw_wide_install_avoiding_spatial_reservation {n : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair)
    (hlenBridge : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained : Finset ℕ) (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (a : Cell n ≃ Fin (n * n))
    (cells : Fin (3 * (n / 450) * (3 * (n + 8))) × Fin 4 → Cell n)
    (spatial prior : Finset (Cell n)) (hcells : Function.Injective cells)
    (hspatial : ∀ x, cells x ∉ spatial) (hprior : ∀ x, cells x ∉ prior)
    (hpriorValues : ∀ c ∈ prior,
      entry a c ∈ priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) :
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (blocks : List DoublePair) (hlen : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
      (a' : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint
        (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ x, cells x ∉ spatial) ∧
      (∀ c ∈ prior, entry a' c = entry a c) ∧
      fwInstalledPairBounds m (poolMaximum n) blocks a'
        (fun x => cells (Fin.cast hlen x.1, x.2)) ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry a' (cells (Fin.cast hlen i, 1)) = entry a' (cells (Fin.cast hlen i, 0)) + gap ∧
        entry a' (cells (Fin.cast hlen i, 2)) = entry a' (cells (Fin.cast hlen i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  obtain ⟨blocks, hlen, a', hvalid, hpair, hav, hplace, hfixed, hbounds, hgap⟩ :=
    fw_reflected_supply_avoiding_all_early_values bmor upper lower sharp hnlo hnhi m hmlo hmhi
      batches hlenBridge retained hretained a cells prior hcells hprior hpriorValues
  exact ⟨blocks, hlen, a', hvalid, hpair, hav, hplace, hspatial, hfixed, hbounds, hgap⟩

/-- If the entries currently occupying the spatial reservation also fit in
the explicit FW10 deletion budget, they may be added to the removed set.
Then every prior and spatial cell is preserved, and the wide blocks avoid both
protected early values and the additional spatial-cell values. No claim is
made here that this extra budget follows from the source's early invoice. -/
theorem fw_wide_install_preserving_spatial_reservation {n : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (protectedValues : Finset ℕ) (a : Cell n ≃ Fin (n * n))
    (cells : Fin (3 * (n / 450) * (3 * (n + 8))) × Fin 4 → Cell n)
    (spatial prior : Finset (Cell n)) (hcells : Function.Injective cells)
    (hspatial : ∀ x, cells x ∉ spatial) (hprior : ∀ x, cells x ∉ prior)
    (hpriorValues : ∀ c ∈ prior, entry a c ∈ protectedValues)
    (hbudget : (protectedValues ∪ spatial.image (entry a)).card +
      4 * (3 * (n / 450) * (3 * (n + 8))) ≤ fwEarlyBudget n) :
    let removed := protectedValues ∪ spatial.image (entry a)
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (blocks : List DoublePair) (hlen : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
      (a' : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint removed) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ c ∈ prior, entry a' c = entry a c) ∧
      (∀ c ∈ spatial, entry a' c = entry a c) ∧
      fwInstalledPairBounds m (poolMaximum n) blocks a'
        (fun x => cells (Fin.cast hlen x.1, x.2)) ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry a' (cells (Fin.cast hlen i, 1)) = entry a' (cells (Fin.cast hlen i, 0)) + gap ∧
        entry a' (cells (Fin.cast hlen i, 2)) = entry a' (cells (Fin.cast hlen i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  dsimp only
  let removed := protectedValues ∪ spatial.image (entry a)
  let reserved := prior ∪ spatial
  have hnew : ∀ x, cells x ∉ reserved := by
    intro x hx
    rcases Finset.mem_union.mp hx with hp | hs
    · exact hprior x hp
    · exact hspatial x hs
  have hreserved : ∀ c ∈ reserved, entry a c ∈ removed := by
    intro c hc
    rcases Finset.mem_union.mp hc with hp | hs
    · exact Finset.mem_union_left _ (hpriorValues c hp)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, hs, rfl⟩)
  obtain ⟨blocks, hlen, a', hvalid, hpair, hav, hplace, hfixed, hbounds, hgap⟩ :=
    fw_reflected_supply_with_sharp_early_budget_and_even_gaps bmor upper lower sharp hnlo hnhi m hmlo hmhi
      removed hbudget a cells reserved hcells hnew hreserved
  refine ⟨blocks, hlen, a', hvalid, hpair, hav, hplace, ?_, ?_, hbounds, hgap⟩
  · intro c hc
    exact hfixed c (Finset.mem_union_left _ hc)
  · intro c hc
    exact hfixed c (Finset.mem_union_right _ hc)

end
end Sude
