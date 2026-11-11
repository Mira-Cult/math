import Sude.FWGroupedPairMassReindex
import Sude.FWBridgeRectangleInvoice
import Sude.FWWideOffsetRectangleInvoice
import Sude.FWOrdinaryStageEighteen

/-! Actual grouped bridge and wide squared pair-incidence bounds on rows and
columns. No diagonal bound or physical placement is asserted. -/
namespace Sude
noncomputable section

theorem fw_grouped_stage_mass_split {P n : ℕ}
    (cells : (Fin P × Fin (6 * (n + 8))) × Bool → Cell n)
    (line : Cell n → Prop) (j : Fin P) :
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (cells ∘ fwBlockPairIndex P n) line (j,b,p)) ^ 2) =
    (∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      (physicalPairLineWeight cells line (j,fwPrefixToControllerPair n
        (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)))) ^ 2) +
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight cells line (j,fwPrefixToControllerPair n
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
          (network,k,edge)))) ^ 2) := by
  classical
  rw [fw_grouped_prefix_stage_squared_pair_mass]
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  calc
    _ = ∑ tag : PrefixStagePair 6 3 n, (physicalPairLineWeight cells line (j,fwPrefixToControllerPair n (e tag))) ^ 2 :=
      (e.sum_comp (fun q => (physicalPairLineWeight cells line (j,fwPrefixToControllerPair n q)) ^ 2)).symm
    _ = _ := by simp [e, prefixStagePairSlot, Fintype.sum_sum_type, Fintype.sum_prod_type]


/-- The bridge grouped row squared incidence is at most eighteen per
stage plus four rectangle incidences globally, given the required derangements. -/
theorem fw_bridge_grouped_row_mass_le_94 {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (hder : ∀ j : Fin 5, ∀ k : Fin 3, ∀ i, (prefixStageLayer rows hr j k).1 i ≠ i) (r : Fin n) :
    (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc)
        (fun z => z.1 = r) (j,b,p)) ^ 2) ≤ 94 := by
  classical
  change (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc ∘ fwBlockPairIndex 5 n)
        (fun z => z.1 = r) (j,b,p)) ^ 2) ≤ 94
  simp_rw [fw_grouped_stage_mass_split]
  rw [Finset.sum_add_distrib]
  have hrects := fw_bridge_reindexed_rectangle_row_invoice hrect hs choice rows cols hr hc r
  have hord : (∑ j : Fin 5, ∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun z => z.1 = r) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) ^ 2) = 90 := by
    simp_rw [fw_bridge_ordinary_row_stage_eq_eighteen hrect hs choice rows cols hr hc _ r (hder _)]
    norm_num
  linarith

theorem fw_bridge_grouped_column_mass_le_94 {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (hder : ∀ j : Fin 5, ∀ k : Fin 3, ∀ i, (prefixStageLayer cols hc j k).1 i ≠ i) (c : Fin n) :
    (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc)
        (fun z => z.2 = c) (j,b,p)) ^ 2) ≤ 94 := by
  classical
  change (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc ∘ fwBlockPairIndex 5 n)
        (fun z => z.2 = c) (j,b,p)) ^ 2) ≤ 94
  simp_rw [fw_grouped_stage_mass_split]
  rw [Finset.sum_add_distrib]
  have hrects := fw_bridge_reindexed_rectangle_column_invoice hrect hs choice rows cols hr hc c
  have hord : (∑ j : Fin 5, ∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun z => z.2 = c) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) ^ 2) = 90 := by
    simp_rw [fw_bridge_ordinary_column_stage_eq_eighteen hrect hs choice rows cols hr hc _ c (hder _)]
    norm_num
  linarith


theorem fw_wide_grouped_row_mass_le {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (hder : ∀ j : Fin (3 * (n / 450)), ∀ k : Fin 3, ∀ i,
      (prefixStageLayer rows hr j k).1 i ≠ i)
    (r : Fin n) :
    (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc)
        (fun z => z.1 = r) (j,b,p)) ^ 2) ≤
      (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4 := by
  classical
  have hrect := fw_wide_reindexed_rectangle_row_invoice hwide hs choice rows cols hr hc r
  have hper (j : Fin (3 * (n / 450))) :=
    fw_wide_ordinary_row_stage_eq_eighteen hwide hs choice rows cols hr hc j r (hder j)
  change (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight ((fwWidePhysicalPairCells hwide hs choice rows cols hr hc) ∘
        fwBlockPairIndex (3 * (n / 450)) n) (fun z => z.1 = r) (j,b,p)) ^ 2) ≤ _
  simp_rw [fw_grouped_stage_mass_split]
  rw [Finset.sum_add_distrib]
  simp_rw [hper]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith


/-- The wide grouped column squared incidence is at most eighteen per
stage plus four rectangle incidences globally, given the required derangements. -/
theorem fw_wide_grouped_column_mass_le {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (hder : ∀ j : Fin (3 * (n / 450)), ∀ k : Fin 3, ∀ i,
      (prefixStageLayer cols hc j k).1 i ≠ i)
    (c : Fin n) :
    (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc)
        (fun z => z.2 = c) (j,b,p)) ^ 2) ≤
      (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4 := by
  classical
  have hrect := fw_wide_reindexed_rectangle_column_invoice hwide hs choice rows cols hr hc c
  have hper (j : Fin (3 * (n / 450))) :=
    fw_wide_ordinary_column_stage_eq_eighteen hwide hs choice rows cols hr hc j c (hder j)
  change (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight ((fwWidePhysicalPairCells hwide hs choice rows cols hr hc) ∘
        fwBlockPairIndex (3 * (n / 450)) n) (fun z => z.2 = c) (j,b,p)) ^ 2) ≤ _
  simp_rw [fw_grouped_stage_mass_split]
  rw [Finset.sum_add_distrib]
  simp_rw [hper]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith




/-- Joint packed row and column lists imply the actual bridge and wide
grouped pair-mass bounds on all rows and columns. Rectangle choice is
arbitrary; no diagonal bound follows from this statement. -/
theorem fw_joint_bridge_wide_grouped_row_column_mass {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc)) :
    (∀ r : Fin n, (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun z => z.1 = r) (j,b,p)) ^ 2) ≤ 94) ∧
    (∀ c : Fin n, (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun z => z.2 = c) (j,b,p)) ^ 2) ≤ 94) ∧
    (∀ r : Fin n, (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun z => z.1 = r) (j,b,p)) ^ 2) ≤ (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4) ∧
    (∀ c : Fin n, (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun z => z.2 = c) (j,b,p)) ^ 2) ≤ (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4) := by
  obtain ⟨hbrd, hbcd, hwrd, hwcd⟩ := fw_joint_bridge_wide_stage_derangements
    br bc sr sc wr wc gr gc hbr hbc hwr hwc reservedRows reservedCols hrows hcols
  exact ⟨fun r => fw_bridge_grouped_row_mass_le_94 hrect hs choice br bc hbr hbc hbrd r,
    fun c => fw_bridge_grouped_column_mass_le_94 hrect hs choice br bc hbr hbc hbcd c,
    fun r => fw_wide_grouped_row_mass_le hwide hs choice wr wc hwr hwc hwrd r,
    fun c => fw_wide_grouped_column_mass_le hwide hs choice wr wc hwr hwc hwcd c⟩

end
end Sude
