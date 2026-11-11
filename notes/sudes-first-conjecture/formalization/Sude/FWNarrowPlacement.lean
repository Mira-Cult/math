import Sude.FWNarrowSeed
import Sude.NarrowSeedPlacement
import Sude.NarrowPoolValues
import Sude.NarrowSeedPlacedMidpoints

/-! Physical FW seed placement in both rectangle and ordinary networks. -/
namespace Sude
noncomputable section

/-- Conditional on the finite seed population and actual bridge/geometry
inputs, select FW's narrowest groups and install genuine gap-two pairs in
both diagonal rectangle families and the two ordinary networks. The source
variance invoice, physical gaps, packing and prior cells are retained. -/
theorem fw_install_narrow_seed (lower : RSIndexLower) (n : ℕ)
    (seeds bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hcount : 3650551 ≤ seeds.card)
    (choice : Fin 384 → Bool) (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = 16 * 3) (hclen : colPerms.length = 16 * 3)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (B : ℕ)
    (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ B)
    (hcapacity : 4 * ((B + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ bridges)
    (hfree : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      packedRectangleCorner (show 2 * 384 + 1 ≤ n by omega) choice
        (Fin.castLE (show 16 * (4 * 6) ≤ 384 by norm_num) x.1, x.2) ∉ base) :
    let Q := 6 * (n + 8)
    let r := 16 + 2 - 1
    let hrect : 16 * (4 * 6) ≤ 384 := by norm_num
    let hs : 2 * 384 + 1 ≤ n := by omega
    let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ Q := by dsimp [Q]; omega
    let hdiag : (4 * 6) * 2 ≤ Q := by dsimp [Q]; omega
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = r * Q), candidates ⊆ seeds ∧
      ∃ (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) (hkept : kept.card = 16),
        (let w := sortedSeedReal candidates r Q hcard
         ∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
          (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
          3 * 6 * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
            (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
        (∀ j : Fin 16, (retainedSeedStageIndex r 16 kept hsub hkept j).val ∈ kept) ∧
        (let R := retainedSeedEndpoints candidates r Q 2 hcard kept hsub
         R.card = 2 * Q * 16 ∧ R ⊆ poolFinset n \ bridges ∧
         ∀ x, x.1.1.val ∉ kept →
           sortedSeedEndpoint candidates r Q 2 hcard x ∈ poolFinset n \ (bridges ∪ R)) ∧
        ∃ (rows cols : List (LayerPacking.Layer n))
          (hrows : rows.length = rowPerms.length) (hcols : cols.length = colPerms.length)
          (b : Cell n ≃ Fin (n * n)),
          rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
          LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
          LayerPacking.PackedLayers (LayerPacking.transposeCells
            ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
          Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
          (∀ x : Fin (16 * (4 * 6)) × Fin 4,
            entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
              sortedSeedEndpoint candidates r Q 2 hcard
                (retainedSeedSlot r 16 Q kept hsub hkept (prefixRectangleInput hdiag x))) ∧
          (∀ x, entry b (LayerPacking.sequenceCell rows x) =
              sortedSeedEndpoint candidates r Q 2 hcard
                (retainedSeedSlot r 16 Q kept hsub hkept
                  (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2)))) ∧
          (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
              sortedSeedEndpoint candidates r Q 2 hcard
                (retainedSeedSlot r 16 Q kept hsub hkept
                  (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2)))) ∧
          (∀ j : Fin 16, ∀ u : Fin (4 * 6), ∀ p : Fin 2,
            entry b (packedRectangleCorner hs choice
              (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p true)) =
            entry b (packedRectangleCorner hs choice
              (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p false)) + 2) ∧
          (∀ i : Fin rows.length, ∀ e : Fin n,
            entry b ((rows.get i).1 e, (rows.get i).2 e) = entry b (e, (rows.get i).2 e) + 2) ∧
          (∀ i : Fin cols.length, ∀ e : Fin n,
            entry b ((cols.get i).2 e, (cols.get i).1 e) = entry b ((cols.get i).2 e, e) + 2) ∧
          (∀ j : Fin 16, ∀ u v : Fin (4 * 6), ∀ p q : Fin 2,
            let group := retainedSeedStageIndex r 16 kept hsub hkept j
            |((entry b (packedRectangleCorner hs choice (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p false)) : ℝ) +
                entry b (packedRectangleCorner hs choice (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p true))) / 2 -
              ((entry b (packedRectangleCorner hs choice (Fin.castLE hrect (finProdFinEquiv (j, v)), prefixPairCorner q false)) : ℝ) +
                entry b (packedRectangleCorner hs choice (Fin.castLE hrect (finProdFinEquiv (j, v)), prefixPairCorner q true))) / 2| ≤
              sortedSeedReal candidates r Q hcard (group.val * Q + (Q - 1)) -
                sortedSeedReal candidates r Q hcard (group.val * Q)) ∧
          (∀ i : Fin rows.length, ∀ e f : Fin n,
            let stage := (finProdFinEquiv.symm (Fin.cast hrlen (Fin.cast hrows i)) : Fin 16 × Fin 3).1
            let group := retainedSeedStageIndex r 16 kept hsub hkept stage
            |((entry b (LayerPacking.sequenceCell rows (i, (e, false))) : ℝ) + entry b (LayerPacking.sequenceCell rows (i, (e, true)))) / 2 -
              ((entry b (LayerPacking.sequenceCell rows (i, (f, false))) : ℝ) + entry b (LayerPacking.sequenceCell rows (i, (f, true)))) / 2| ≤
              sortedSeedReal candidates r Q hcard (group.val * Q + (Q - 1)) - sortedSeedReal candidates r Q hcard (group.val * Q)) ∧
          (∀ i : Fin cols.length, ∀ e f : Fin n,
            let stage := (finProdFinEquiv.symm (Fin.cast hclen (Fin.cast hcols i)) : Fin 16 × Fin 3).1
            let group := retainedSeedStageIndex r 16 kept hsub hkept stage
            |((entry b (LayerPacking.sequenceCell cols (i, (e, false))).swap : ℝ) + entry b (LayerPacking.sequenceCell cols (i, (e, true))).swap) / 2 -
              ((entry b (LayerPacking.sequenceCell cols (i, (f, false))).swap : ℝ) + entry b (LayerPacking.sequenceCell cols (i, (f, true))).swap) / 2| ≤
              sortedSeedReal candidates r Q hcard (group.val * Q + (Q - 1)) - sortedSeedReal candidates r Q hcard (group.val * Q)) ∧
          (∀ c ∈ base, entry b c = entry a c) := by
  dsimp only
  let Q := 6 * (n + 8)
  let r := 16 + 2 - 1
  have hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ Q := by dsimp [Q]; omega
  have hdiag : (4 * 6) * 2 ≤ Q := by dsimp [Q]; omega
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hrect : 16 * (4 * 6) ≤ 384 := by norm_num
  have hs : 2 * 384 + 1 ≤ n := by omega
  obtain ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, hinj, hav⟩ :=
    fw_actual_narrow_seed lower n seeds bridges hnlo hnhi hseed hprime hbridge hcount
  let values := retainedSeedPoolValues candidates r 16 Q 2 hcard kept hsub hkept bridges hav
  let R := retainedSeedEndpoints candidates r Q 2 hcard kept hsub
  have hRcard : R.card = 2 * Q * 16 := by
    dsimp [R, retainedSeedEndpoints]
    rw [Finset.card_image_of_injective _ hinj, retainedSeedLabels_card, hkept]
  have hRsub : R ⊆ poolFinset n \ bridges := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact hav x
  have hdiscard : ∀ x, x.1.1.val ∉ kept →
      sortedSeedEndpoint candidates r Q 2 hcard x ∈ poolFinset n \ (bridges ∪ R) := by
    intro x hx
    have havx := Finset.mem_sdiff.mp (hav x)
    have hnot := discardedSeedEndpoint_not_retained candidates r Q 2 hcard hinj kept hsub x hx
    refine Finset.mem_sdiff.mpr ⟨havx.1, ?_⟩
    intro hm
    rcases Finset.mem_union.mp hm with hb | hret
    · exact havx.2 hb
    · exact hnot hret
  obtain ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdis,
    hplaced, hrplaced, hcplaced, hrgap, hcgap, hfixed⟩ :=
    install_retained_seed_pairs candidates hcard kept hsub hkept bridges hav hinj
      hfit hdiag hrect hs choice rowPerms colPerms hrlen hclen hrderange hcderange
      base hrload hcload hcapacity a hbase hfree
  refine ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance,
    retainedSeedStageIndex_mem r 16 kept hsub hkept, ⟨hRcard, hRsub, hdiscard⟩, rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdis,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfixed⟩
  · intro x
    exact hplaced x
  · intro x
    exact hrplaced x
  · intro x
    exact hcplaced x
  · intro j u p
    change entry b (packedRectangleCorner hs choice
      (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p true)) =
      entry b (packedRectangleCorner hs choice
        (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p false)) + 2
    rw [hplaced (finProdFinEquiv (j, u), prefixPairCorner p true),
      hplaced (finProdFinEquiv (j, u), prefixPairCorner p false)]
    simp only [prefixRectangleInput_pair]
    exact retainedSeedPoolValues_gap candidates r 16 Q 2 hcard kept hsub hkept bridges hav
      j (prefixDiagonalPairIndex hdiag (u, p))
  · intro i e
    have h := hrgap i e
    simpa [variablePrefixNetworkGap] using h
  · intro i e
    have h := hcgap i e
    simpa [variablePrefixNetworkGap] using h
  · intro j u v p q
    exact retainedSeed_placed_rectangle_midpoints candidates hcard kept hsub hkept bridges hav
      hQ hdiag b (fun x => packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2))
      hplaced j u v p q
  · intro i e f
    rw [hrplaced (i, (e, false)), hrplaced (i, (e, true)),
      hrplaced (i, (f, false)), hrplaced (i, (f, true))]
    exact retainedSeed_network_midpoints candidates hcard kept hsub hkept bridges hav
      hQ hfit hrlen 0 (Fin.cast hrows i) e f
  · intro i e f
    rw [hcplaced (i, (e, false)), hcplaced (i, (e, true)),
      hcplaced (i, (f, false)), hcplaced (i, (f, true))]
    exact retainedSeed_network_midpoints candidates hcard kept hsub hkept bridges hav
      hQ hfit hclen 1 (Fin.cast hcols i) e f

end
end Sude
