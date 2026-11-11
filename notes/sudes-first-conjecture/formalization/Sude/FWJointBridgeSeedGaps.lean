import Sude.FWPhysicalBridgeWideTrace
import Sude.FWPhysicalEdgeWitnessGrid

/-! Oriented ordinary bridge and seed gaps on the actual preserved square.
These facts do not claim physical disjointness or any network switch. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Every actual bridge layer has its designated high endpoint at least its
low endpoint in each orientation, using the same selected bridge batches. -/
theorem fw_preserved_bridge_layers_ordered {n L : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) :
    (∀ i e, entry grown (e, (rows.get i).2 e) ≤ entry grown ((rows.get i).1 e, (rows.get i).2 e)) ∧
    (∀ i e, entry grown ((cols.get i).2 e, e) ≤ entry grown ((cols.get i).2 e, (cols.get i).1 e)) := by
  constructor
  · intro i e
    let jk : Fin 5 × Fin 3 := finProdFinEquiv.symm (Fin.cast hr i)
    have hi : Fin.cast hr.symm (finProdFinEquiv jk) = i := by
      dsimp only [jk]
      rw [Equiv.apply_symm_apply, Fin.cast_cast]
      rfl
    have h := (fw_preserved_bridge_ordinary_gap batches hvalid hrect hseed hwide hs choice rows cols hr hc
      sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace jk.1 (jk.2, e) false).2.2
    simp only [fwBridgeLayerCells, Bool.false_eq_true, ↓reduceIte, fwBridgeLayerIndex] at h
    rw [hi] at h
    change entry grown ((rows.get i).1 e, (rows.get i).2 e) =
      entry grown (e, (rows.get i).2 e) + _ at h
    omega
  · intro i e
    let jk : Fin 5 × Fin 3 := finProdFinEquiv.symm (Fin.cast hc i)
    have hi : Fin.cast hc.symm (finProdFinEquiv jk) = i := by
      dsimp only [jk]
      rw [Equiv.apply_symm_apply, Fin.cast_cast]
      rfl
    have h := (fw_preserved_bridge_ordinary_gap batches hvalid hrect hseed hwide hs choice rows cols hr hc
      sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace jk.1 (jk.2, e) true).2.2
    simp only [fwBridgeLayerCells, ↓reduceIte, fwBridgeLayerIndex] at h
    rw [hi] at h
    change entry grown ((cols.get i).2 e, (cols.get i).1 e) =
      entry grown ((cols.get i).2 e, e) + _ at h
    omega

/-- Every actual retained-seed layer has oriented gap two in either network,
after preserving the ordinary seed cells. -/
theorem fw_preserved_seed_layers_gap_two {n : ℕ}
    (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ x, entry grown (fwSeedOrdinaryCells sr sc hsr hsc x) =
      entry old (fwSeedOrdinaryCells sr sc hsr hsc x))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) :
    (∀ i e, entry grown ((sr.get i).1 e, (sr.get i).2 e) = entry grown (e, (sr.get i).2 e) + 2) ∧
    (∀ i e, entry grown ((sc.get i).2 e, (sc.get i).1 e) = entry grown ((sc.get i).2 e, e) + 2) := by
  constructor
  · intro i e
    let jk : Fin 16 × Fin 3 := finProdFinEquiv.symm (Fin.cast hsr i)
    have hi : Fin.cast hsr.symm (finProdFinEquiv jk) = i := by
      dsimp only [jk]
      rw [Equiv.apply_symm_apply, Fin.cast_cast]
      rfl
    have h := fw_seed_edge_gap_after_preservation batches candidates hcard kept hsub hkept hav
      sr sc hsr hsc old grown hfixed hso (jk.2, e) false jk.1
    simp only [fwSeedEdgeCells, Bool.false_eq_true, ↓reduceIte, fwSeedOrdinaryCells] at h
    rw [hi] at h
    simpa [LayerPacking.sequenceCell, LayerPacking.layerCell] using h
  · intro i e
    let jk : Fin 16 × Fin 3 := finProdFinEquiv.symm (Fin.cast hsc i)
    have hi : Fin.cast hsc.symm (finProdFinEquiv jk) = i := by
      dsimp only [jk]
      rw [Equiv.apply_symm_apply, Fin.cast_cast]
      rfl
    have h := fw_seed_edge_gap_after_preservation batches candidates hcard kept hsub hkept hav
      sr sc hsr hsc old grown hfixed hso (jk.2, e) true jk.1
    simp only [fwSeedEdgeCells, ↓reduceIte, fwSeedOrdinaryCells] at h
    rw [hi] at h
    simpa [LayerPacking.sequenceCell, LayerPacking.layerCell, Prod.swap_prod_mk] using h

/-- The full early-role preservation condition supplies the ordered bridge
and retained-seed network layers on the very same grown square. -/
theorem fw_preserved_bridge_seed_layers_ordered {n L : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) :
    (∀ i e, entry grown (e, (rows.get i).2 e) ≤ entry grown ((rows.get i).1 e, (rows.get i).2 e)) ∧
    (∀ i e, entry grown ((cols.get i).2 e, e) ≤ entry grown ((cols.get i).2 e, (cols.get i).1 e)) ∧
    (∀ i e, entry grown (e, (sr.get i).2 e) ≤ entry grown ((sr.get i).1 e, (sr.get i).2 e)) ∧
    (∀ i e, entry grown ((sc.get i).2 e, e) ≤ entry grown ((sc.get i).2 e, (sc.get i).1 e)) := by
  have hseedfixed : ∀ x, entry grown (fwSeedOrdinaryCells sr sc hsr hsc x) =
      entry old (fwSeedOrdinaryCells sr sc hsr hsc x) := by
    intro x
    apply hfixed
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)))
  obtain ⟨hbr, hbc⟩ := fw_preserved_bridge_layers_ordered batches hvalid hrect hseed hwide hs choice
    rows cols hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace
  obtain ⟨hsr', hsc'⟩ := fw_preserved_seed_layers_gap_two batches candidates hcard kept hsub hkept
    hav sr sc hsr hsc old grown hseedfixed hso
  refine ⟨hbr, hbc, ?_, ?_⟩
  · intro i e
    have h := hsr' i e
    omega
  · intro i e
    have h := hsc' i e
    omega

end
end Sude
