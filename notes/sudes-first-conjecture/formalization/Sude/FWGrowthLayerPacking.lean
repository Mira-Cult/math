import Sude.FWWideLayerPacking
import Sude.FWRectangleCapacity

/-! Conditional packing of supplied growth-stage layers after the FW early
layout. No trace existence, source-stage cap or crossing is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- The first-window trace cap implies the remaining Hall load inequality in
the first FW order band, including all already allocated wide layers. -/
theorem fw_growth_layer_hall_bound {n P : ℕ} (hnlo : 19485 ≤ n) (_hnhi : n ≤ 35733)
    (hP : P ≤ 238) : 4 * ((254 + 36 * (n / 450)) + 12 * P) + 8 < n := by
  have := Nat.mul_div_le n 450
  omega

/-- A supplied prefix allowance leaves room for the actual number of
growth-stage rectangles after bridge, retained-seed and wide labels. -/
theorem fw_growth_offset_rectangle_capacity {n P P₀ : ℕ} (hP : 16 + P ≤ P₀) :
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) + P * (4 * 6) ≤
      fwJointRectangleCount n P₀ := by
  unfold fwJointRectangleCount
  omega

/-- Given the actual early packing and a supplied derangement triple, construct
both growing-trace layer families after all six early layer supports and the
entire rectangle support. The packing is geometric; no values are installed. -/
theorem fw_pack_growth_layers_after_wide {n L P : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : P ≤ 238)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (p : Fin 3 → Equiv.Perm (Fin n)) (hder : ∀ k e, p k e ≠ e)
    (br bc sr sc wr wc : List (LayerPacking.Layer n))
    (hbrlen : br.length = 5 * 3) (hbclen : bc.length = 5 * 3)
    (hsrlen : sr.length = 16 * 3) (hsclen : sc.length = 16 * 3)
    (hwrlen : wr.length = (3 * (n / 450)) * 3)
    (hwclen : wc.length = (3 * (n / 450)) * 3)
    (hbr : LayerPacking.PackedLayers (packedRectangleSupport hs choice) br)
    (hbc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br)) bc)
    (hsr : LayerPacking.PackedLayers
      ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) sr)
    (hsc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr)) sc)
    (hwr : LayerPacking.PackedLayers
      ((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hwc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪ LayerPacking.layersSupport wr)) wc) :
    let base := ((((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪ LayerPacking.layersSupport wr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport wc))
    ∃ (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * 3) (hc : cols.length = P * 3),
      rows.map Prod.fst = bridgeRepeatedPermutations P p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations P p ∧
      LayerPacking.PackedLayers base rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ (j : Fin P) (k : Fin 3) (e : Fin n),
        (rows.get (bridgeStageLayerIndex hr j k)).1 e = p k e ∧
        (cols.get (bridgeStageLayerIndex hc j k)).1 e = p k e) := by
  dsimp only
  let old := ((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport sc))
  let base := (old ∪ LayerPacking.layersSupport wr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc)
  obtain ⟨hrowOld, hcolOld, _⟩ := fw_pack_wide_layers_after_bridge_seed hnlo hs choice p hder
    br bc sr sc hbrlen hbclen hsrlen hsclen hbr hbc hsr hsc
  obtain ⟨hrow1, hcol1⟩ := hwr.union_load hrowOld hcolOld
  obtain ⟨hrow2, hcol2⟩ := fw_transposed_layer_union_load hwc hrow1 hcol1
  have hrowBase : ∀ i, (LayerPacking.rowUsed base i).card ≤ 254 + 36 * (n / 450) := by
    intro i
    have h := hrow2 i
    rw [hwrlen, hwclen] at h
    dsimp [base, old]
    omega
  have hcolBase : ∀ i, (LayerPacking.colUsed base i).card ≤ 254 + 36 * (n / 450) := by
    intro i
    have h := hcol2 i
    rw [hwrlen, hwclen] at h
    dsimp [base, old]
    omega
  let perms := bridgeRepeatedPermutations P p
  have hperms : perms.length = P * 3 := bridgeRepeatedPermutations_length p
  have hder' : ∀ π ∈ perms, ∀ i, π i ≠ i := bridgeRepeatedPermutations_derange p hder
  have hguard := fw_growth_layer_hall_bound hnlo hnhi hP
  have hnrow : 4 * ((254 + 36 * (n / 450)) + 2 * perms.length) + 8 < n := by
    rw [hperms]
    omega
  obtain ⟨rows, hrmap, hrpacked⟩ := LayerPacking.pack_finite_layers perms base hder' hrowBase hcolBase hnrow
  have hr : rows.length = P * 3 := by
    have h := congrArg List.length hrmap
    simpa [hperms] using h
  obtain ⟨hrload, hcload⟩ := hrpacked.union_load hrowBase hcolBase
  have hrowT : ∀ i, (LayerPacking.rowUsed (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) i).card ≤ (254 + 36 * (n / 450)) + 2 * (P * 3) := by
    intro i
    simpa [hr] using hcload i
  have hcolT : ∀ i, (LayerPacking.colUsed (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) i).card ≤ (254 + 36 * (n / 450)) + 2 * (P * 3) := by
    intro i
    simpa [hr] using hrload i
  have hncol : 4 * (((254 + 36 * (n / 450)) + 2 * (P * 3)) + 2 * perms.length) + 8 < n := by
    rw [hperms]
    omega
  obtain ⟨cols, hcmap, hcpacked⟩ := LayerPacking.pack_finite_layers perms
    (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport rows)) hder' hrowT hcolT hncol
  have hc : cols.length = P * 3 := by
    have h := congrArg List.length hcmap
    simpa [hperms] using h
  have hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hzrow hzcol
    exact (hcpacked.transposed_support_safe z hzcol).1 (Finset.mem_union_right base hzrow)
  refine ⟨rows, cols, hr, hc, hrmap, hcmap, hrpacked, hcpacked, hdisjoint, ?_⟩
  intro j k e
  exact ⟨bridgeStageLayer_endpoints rows hr p hrmap j k e,
    bridgeStageLayer_endpoints cols hc p hcmap j k e⟩

end
end Sude
