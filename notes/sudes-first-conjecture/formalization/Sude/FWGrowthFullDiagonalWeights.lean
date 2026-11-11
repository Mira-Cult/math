import Sude.FWGrowthDiagonalPhysical

/-! The exact diagonal incidence of every growth-stage pair slot. -/
namespace Sude
noncomputable section

/-- Under balanced rectangle choice and supplied packed layers, the full
physical diagonal weights are the indicator functions of the respective
12-slot groups; partners and ordinary slots contribute neither weight. -/
theorem fw_growth_full_diagonal_weights {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * 3)
    (hc : cols.length = P * 3) (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (j : Fin P)
    (hchoice : ∀ rect : Fin (4*6),
      choice (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) = decide (rect.val < 12))
    (i : Fin (6*(n+8))) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    physicalPairLineWeight cells (fun c => c ∈ mainCells n) (j,i) =
      (if i ∈ fwGrowthMainSlots n then 1 else 0) ∧
    physicalPairLineWeight cells (fun c => c ∈ antiCells n) (j,i) =
      (if i ∈ fwGrowthAntiSlots n then 1 else 0) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  have hd := fw_growth_slot_groups_disjoint n
  by_cases hm : i ∈ fwGrowthMainSlots n
  · have ha : i ∉ fwGrowthAntiSlots n := fun h => (Finset.disjoint_left.mp hd.1) hm h
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hm
    have hw := fw_growth_balanced_rectangle_weights offset hoff hs hL choice rows cols hr hc j hchoice
      ⟨a.val, by have := a.isLt; omega⟩ 0
    have hmain : prefixDiagonalPairIndex (d := 6) (Q := 6*(n+8)) (by omega)
        (⟨a.val, by have := a.isLt; omega⟩,0) ∈ fwGrowthMainSlots n :=
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    simp only [hmain, ha, ↓reduceIte]
    simpa using hw
  · by_cases ha : i ∈ fwGrowthAntiSlots n
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
      have hw := fw_growth_balanced_rectangle_weights offset hoff hs hL choice rows cols hr hc j hchoice
        ⟨a.val+12, by have := a.isLt; omega⟩ 0
      have hanti : prefixDiagonalPairIndex (d := 6) (Q := 6*(n+8)) (by omega)
          (⟨a.val+12, by have := a.isLt; omega⟩,0) ∈ fwGrowthAntiSlots n :=
        Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      simp only [hm, hanti, ↓reduceIte]
      have hnot : ¬ a.val+12 < 12 := by omega
      simpa [hnot] using hw
    · by_cases hp : i ∈ fwGrowthPartnerSlots n
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
        have hw := fw_growth_balanced_rectangle_weights offset hoff hs hL choice rows cols hr hc j hchoice a 1
        simp only [hm, ha, ↓reduceIte]
        simpa using hw
      · have ho : i ∈ fwGrowthOrdinarySlots n := by
          rw [fw_growth_ordinary_slots_eq_complement]
          simp [hm, ha, hp]
        obtain ⟨⟨tag,k,edge⟩, _, rfl⟩ := Finset.mem_image.mp ho
        have hf := fw_growth_ordinary_off_diagonals offset hoff hs choice rows cols hr hc
          reservedRows reservedCols hrows hcols j tag k edge false
        have ht := fw_growth_ordinary_off_diagonals offset hoff hs choice rows cols hr hc
          reservedRows reservedCols hrows hcols j tag k edge true
        simp only [hm, ha, ↓reduceIte]
        simp [physicalPairLineWeight, hf.1, hf.2, ht.1, ht.2]

end
end Sude
