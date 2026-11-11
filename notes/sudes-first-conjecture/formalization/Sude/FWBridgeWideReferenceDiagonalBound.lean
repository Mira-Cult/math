import Sude.FWBridgeWideDiagonalSignedScore
import Sude.FWThetaBridgeSourceGap
import Sude.FWStageVaryingBridgeGrid
import Sude.LayerPackingSegments
import Sude.FWSelectedThetaWitness
import Sude.FWThetaProjectedFreshWideWitness

/-! Diagonal difference bounds for the grouped bridge and wide active-role
families on the ordered and network-reference squares of a theta witness. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- Every bridge block gap at stage `j` lies in the nominal stage window
`((208 / 231) * bridgeSpan X R_j, bridgeSpan X R_j)`. -/
theorem fw_theta_bridge_gap_in_span {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (j : Fin 5) (b : Fin (3 * (n + 8))) :
    let X : ℝ := poolMaximum n
    let R := fwBridgeRadius X j.val
    (208 / 231 : ℝ) * bridgeSpan X R < (f.gapb j b : ℝ) ∧
      (f.gapb j b : ℝ) < bridgeSpan X R := by
  dsimp only
  rw [fw_theta_bridge_source_gap f j b]
  have hv : FWBridgeBatchValid n ∅ f.batches j.val := (f.hvalid j.val j.isLt).1
  have hi : (f.πb j b).val < (f.batches j.val).length := by rw [hv.1]; exact (f.πb j b).isLt
  have hb := hv.2.2.2.2 (f.batches j.val)[(f.πb j b).val] (List.getElem_mem hi)
  simp only [selectedBridgeGap, List.getElem?_eq_getElem hi]
  exact ⟨hb.2.2.1, hb.2.2.2.1⟩

/-- The five-stage bridge signed-gap contrast is bounded by
`(613256873 / 949132107) * poolMaximum n`. -/
theorem fw_theta_bridge_signed_gap_contrast {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) :
    |(1 / 2 : ℝ) * ((∑ j : Fin 5, ∑ b ∈ fwWideSignedGapSlots n true, (f.gapb j b : ℝ)) -
      ∑ j : Fin 5, ∑ b ∈ fwWideSignedGapSlots n false, (f.gapb j b : ℝ))| ≤
      (613256873 / 949132107 : ℝ) * (poolMaximum n : ℝ) := by
  classical
  let X : ℝ := poolMaximum n
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hstage (j : Fin 5) :
      |(∑ b ∈ fwWideSignedGapSlots n true, (f.gapb j b : ℝ)) -
        (∑ b ∈ fwWideSignedGapSlots n false, (f.gapb j b : ℝ))| ≤
        (12 : ℝ) * ((23 / 231 : ℝ) * bridgeSpan X (fwBridgeRadius X j.val)) := by
    rw [fwWideSignedGapSlots, fwWideSignedGapSlots,
      Finset.sum_image (by intro a _ b _ h; exact fw_wide_signed_gap_slot_injective n true h),
      Finset.sum_image (by intro a _ b _ h; exact fw_wide_signed_gap_slot_injective n false h),
      ← Finset.sum_sub_distrib]
    calc
      |∑ r : Fin 12, ((f.gapb j (fwWideSignedGapSlot n true r) : ℝ) -
          (f.gapb j (fwWideSignedGapSlot n false r) : ℝ))|
        ≤ ∑ r : Fin 12, |(f.gapb j (fwWideSignedGapSlot n true r) : ℝ) -
            (f.gapb j (fwWideSignedGapSlot n false r) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin 12, ((23 / 231 : ℝ) * bridgeSpan X (fwBridgeRadius X j.val)) := by
        apply Finset.sum_le_sum
        intro r _
        have ht := fw_theta_bridge_gap_in_span f j (fwWideSignedGapSlot n true r)
        have hf := fw_theta_bridge_gap_in_span f j (fwWideSignedGapSlot n false r)
        dsimp only at ht hf
        rw [abs_le]
        constructor <;> linarith
      _ = (12 : ℝ) * ((23 / 231 : ℝ) * bridgeSpan X (fwBridgeRadius X j.val)) := by simp
  have hspan (j : Fin 5) :
      bridgeSpan X (fwBridgeRadius X j.val) = min (fwBridgeRatio j.val) (1 / 2) * X := by
    rw [min_mul_of_nonneg _ _ (le_of_lt hX)]
    simp only [bridgeSpan, fwBridgeRadius]
    congr 1; ring
  rw [← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    (1 / 2 : ℝ) * |∑ j : Fin 5, ((∑ b ∈ fwWideSignedGapSlots n true, (f.gapb j b : ℝ)) -
        (∑ b ∈ fwWideSignedGapSlots n false, (f.gapb j b : ℝ)))|
      ≤ (1 / 2 : ℝ) * ∑ j : Fin 5, |(∑ b ∈ fwWideSignedGapSlots n true, (f.gapb j b : ℝ)) -
          (∑ b ∈ fwWideSignedGapSlots n false, (f.gapb j b : ℝ))| := by
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∑ j : Fin 5, (12 : ℝ) * ((23 / 231 : ℝ) * bridgeSpan X (fwBridgeRadius X j.val)) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hstage j)) (by norm_num)
    _ = (613256873 / 949132107 : ℝ) * X := by
        simp_rw [hspan]
        have hs := fw_bridge_five_stage_schedule
        rw [Fin.sum_univ_five]
        simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
          show (3 : Fin 5).val = 3 from rfl, show (4 : Fin 5).val = 4 from rfl,
          hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1]
        norm_num
        ring

/-- Subtracting two `double_block_actual_selected_line_identity` equations
with equal stage weight sums cancels the stage-mean baseline. -/
theorem double_block_diagonal_difference_of_equal_weights {n P : ℕ}
    (cells : (Fin P × Fin (3 * (n + 8)) × Fin 2) × Bool → Cell n)
    (hcells : Function.Injective cells)
    (old new : Cell n ≃ Fin (n * n))
    (gap : Fin P → Fin (3 * (n + 8)) → ℕ)
    (hgap : ∀ j b p, entry new (cells ((j, b, p), true)) = entry new (cells ((j, b, p), false)) + gap j b)
    (hwMain : ∀ j : Fin P, (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells (fun c => c ∈ mainCells n) j b) = 12)
    (hwAnti : ∀ j : Fin P, (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells (fun c => c ∈ antiCells n) j b) = 12)
    (horMain : ∀ j : Fin P,
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
        physicalPairLineOrientation cells (fun c => c ∈ mainCells n) (j, b, p) * ((gap j b : ℝ) / 2)) =
      -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n true, (gap j b : ℝ))
    (horAnti : ∀ j : Fin P,
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
        physicalPairLineOrientation cells (fun c => c ∈ antiCells n) (j, b, p) * ((gap j b : ℝ) / 2)) =
      -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n false, (gap j b : ℝ)) :
    ((∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ mainCells n), (entry new c : ℝ)) -
      (∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ antiCells n), (entry new c : ℝ))) =
    (doubleBlockActualCenteredScore cells (fun c => c ∈ mainCells n) old new -
      doubleBlockActualCenteredScore cells (fun c => c ∈ antiCells n) old new) -
    (1 / 2 : ℝ) * ((∑ j : Fin P, ∑ b ∈ fwWideSignedGapSlots n true, (gap j b : ℝ)) -
      ∑ j : Fin P, ∑ b ∈ fwWideSignedGapSlots n false, (gap j b : ℝ)) := by
  classical
  have hm := double_block_actual_selected_line_identity cells hcells (fun c => c ∈ mainCells n) old new
  have ha := double_block_actual_selected_line_identity cells hcells (fun c => c ∈ antiCells n) old new
  have hmeanEq :
      (∑ j : Fin P, ∑ b : Fin (3 * (n + 8)),
        doubleBlockLineWeight cells (fun c => c ∈ mainCells n) j b * doubleStageMidpointMean cells old j) =
      (∑ j : Fin P, ∑ b : Fin (3 * (n + 8)),
        doubleBlockLineWeight cells (fun c => c ∈ antiCells n) j b * doubleStageMidpointMean cells old j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, ← Finset.sum_mul, hwMain j, hwAnti j]
  have hgapTerm (line : Cell n → Prop) [DecidablePred line] (j : Fin P) :
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
        physicalPairLineOrientation cells line (j, b, p) *
          (((entry new (cells ((j, b, p), true)) : ℝ) - entry new (cells ((j, b, p), false))) / 2)) =
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
        physicalPairLineOrientation cells line (j, b, p) * ((gap j b : ℝ) / 2)) := by
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro p _
    congr 2
    have hg : (entry new (cells ((j, b, p), true)) : ℝ) =
        (entry new (cells ((j, b, p), false)) : ℝ) + (gap j b : ℝ) := by
      exact_mod_cast hgap j b p
    linarith
  simp_rw [hgapTerm (fun c => c ∈ mainCells n), horMain, ← Finset.mul_sum] at hm
  simp_rw [hgapTerm (fun c => c ∈ antiCells n), horAnti, ← Finset.mul_sum] at ha
  rw [hm, ha, hmeanEq]
  ring

/-- Every diagonal cell in the bridge or wide pair image lies in
`packedRectangleSupport`, so `oldReference` and `f.ordered` agree on it. -/
theorem fw_bridge_wide_diagonal_reference_sum_eq {n L : ℕ}
    (choice : Fin L → Bool) (f : FWThetaFamilyWitness n L choice)
    (oldReference : Cell n ≃ Fin (n * n))
    (hrect_fixed : ∀ z ∈ packedRectangleSupport f.hs choice, entry oldReference z = entry f.ordered z)
    (line : Cell n → Prop) [DecidablePred line]
    (hline : ∀ z, line z → z ∈ mainCells n ∪ antiCells n) :
    let bridge := fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
    let wide := fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
    (∑ z ∈ (Finset.univ.image bridge).filter line, (entry oldReference z : ℝ)) =
      (∑ z ∈ (Finset.univ.image bridge).filter line, (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image wide).filter line, (entry oldReference z : ℝ)) =
      (∑ z ∈ (Finset.univ.image wide).filter line, (entry f.ordered z : ℝ)) := by
  classical
  dsimp only
  let reservedRows := packedRectangleSupport f.hs choice
  let reservedCols := LayerPacking.transposeCells
    (reservedRows ∪ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr))
  let bridge := fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
  let wide := fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
  have hbridge_im : Finset.univ.image bridge =
      Finset.univ.image (fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc) := by
    change Finset.univ.image (fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc ∘ fwBlockPairIndex 5 n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex 5 n).surjective]
  have hwide_im : Finset.univ.image wide =
      Finset.univ.image (fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc) := by
    change Finset.univ.image (fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc ∘ fwBlockPairIndex (3 * (n / 450)) n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex (3 * (n / 450)) n).surjective]
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  constructor
  · apply Finset.sum_congr rfl
    intro z hz
    rw [hbridge_im] at hz
    obtain ⟨hz_im, hz_line⟩ := Finset.mem_filter.mp hz
    obtain ⟨⟨⟨j, q⟩, side⟩, _, hzeq⟩ := Finset.mem_image.mp hz_im
    obtain ⟨tag, htag⟩ := (fwPrefixToControllerPair n).surjective q
    rw [← htag] at hzeq
    obtain ⟨ptag, rfl⟩ := e.surjective tag
    cases ptag with
    | inl x =>
      rcases x with ⟨rect, pair⟩
      have hcell : fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
          ((j, fwPrefixToControllerPair n (prefixDiagonalPairIndex hdiag (rect, pair))), side) =
          packedRectangleCorner f.hs choice
            (bridgeDiagonalRectangle f.hrect (finProdFinEquiv (j, rect)), prefixPairCorner pair side) :=
        fw_bridge_reindexed_diagonal_cell f.hrect f.hs choice f.br f.bc f.hbr f.hbc j rect pair side
      have hz_rect : z ∈ packedRectangleSupport f.hs choice := by
        rw [← hzeq]
        change fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
          ((j, fwPrefixToControllerPair n (prefixDiagonalPairIndex hdiag (rect, pair))), side) ∈ _
        rw [hcell]
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      exact_mod_cast hrect_fixed z hz_rect
    | inr x =>
      rcases x with ⟨network, k, edge⟩
      have hoff := fw_bridge_ordinary_cell_off_diagonals f.hrect f.hs choice
        f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc reservedRows reservedCols f.hrows f.hcols
        j network k edge side
      rw [← hzeq] at hz_line
      rcases Finset.mem_union.mp (hline _ hz_line) with hm | ha
      · exact False.elim (hoff.1 hm)
      · exact False.elim (hoff.2 ha)
  · apply Finset.sum_congr rfl
    intro z hz
    rw [hwide_im] at hz
    obtain ⟨hz_im, hz_line⟩ := Finset.mem_filter.mp hz
    obtain ⟨⟨⟨j, q⟩, side⟩, _, hzeq⟩ := Finset.mem_image.mp hz_im
    obtain ⟨tag, htag⟩ := (fwPrefixToControllerPair n).surjective q
    rw [← htag] at hzeq
    obtain ⟨ptag, rfl⟩ := e.surjective tag
    cases ptag with
    | inl x =>
      rcases x with ⟨rect, pair⟩
      have hcell : fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
          ((j, fwPrefixToControllerPair n (prefixDiagonalPairIndex hdiag (rect, pair))), side) =
          packedRectangleCorner f.hs choice
            (fwWideRectangle f.hwide (finProdFinEquiv (j, rect)), prefixPairCorner pair side) :=
        fw_wide_reindexed_diagonal_cell f.hwide f.hs choice f.wr f.wc f.hwr f.hwc j rect pair side
      have hz_rect : z ∈ packedRectangleSupport f.hs choice := by
        rw [← hzeq]
        change fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
          ((j, fwPrefixToControllerPair n (prefixDiagonalPairIndex hdiag (rect, pair))), side) ∈ _
        rw [hcell]
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      exact_mod_cast hrect_fixed z hz_rect
    | inr x =>
      rcases x with ⟨network, k, edge⟩
      have hoff := fw_wide_ordinary_cell_off_diagonals f.hwide f.hs choice
        f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hwr f.hwc reservedRows reservedCols f.hrows f.hcols
        j network k edge side
      rw [← hzeq] at hz_line
      rcases Finset.mem_union.mp (hline _ hz_line) with hm | ha
      · exact False.elim (hoff.1 hm)
      · exact False.elim (hoff.2 ha)

/-- Diagonal difference bounds for bridge and wide families for an abstract `choice`. -/
theorem fw_bridge_wide_diagonal_differences_of_choice {n P : ℕ}
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (oldReference : Cell n ≃ Fin (n * n))
    (hrect_fixed : ∀ z ∈ packedRectangleSupport f.hs choice, entry oldReference z = entry f.ordered z)
    (hL : 3 ≤ fwJointRectangleCount n 254)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (otherG : Fin (fwJointRectangleCount n 254) → Bool)
    (hchoice_eq : fwBridgeSeedWideGrowthChoice f.hrect f.hseedrect f.hwide hgrowth otherG = choice)
    (hwgap : |(1 / 2 : ℝ) * ((∑ j : Fin (3 * (n / 450)), ∑ b ∈ fwWideSignedGapSlots n true, (f.gapw j b : ℝ)) -
      ∑ j : Fin (3 * (n / 450)), ∑ b ∈ fwWideSignedGapSlots n false, (f.gapw j b : ℝ))| <
      2 * Real.sqrt ((3 / 2 : ℝ) * (3 * ((n / 450 : ℕ) : ℝ)) * ((64 / 235 : ℝ) * (poolMaximum n : ℝ))^2 * Real.log 16)) :
    let bridge := fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
    let wide := fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
    let X : ℝ := poolMaximum n
    let k := ((n / 450 : ℕ) : ℝ)
    let B := X * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8))
    let W := X * (2 / 235 : ℝ) * Real.sqrt ((54 * k + 4) * Real.log (8 * (n : ℝ) + 8))
    let E := Real.sqrt ((3 / 2 : ℝ) * (3 * k) * ((64 / 235 : ℝ) * X)^2 * Real.log 16)
    |(∑ z ∈ (Finset.univ.image bridge).filter (fun z => z ∈ mainCells n), (entry oldReference z : ℝ)) -
      (∑ z ∈ (Finset.univ.image bridge).filter (fun z => z ∈ antiCells n), (entry oldReference z : ℝ))| <
      2 * B + (613256873 / 949132107 : ℝ) * X ∧
    |(∑ z ∈ (Finset.univ.image wide).filter (fun z => z ∈ mainCells n), (entry oldReference z : ℝ)) -
      (∑ z ∈ (Finset.univ.image wide).filter (fun z => z ∈ antiCells n), (entry oldReference z : ℝ))| <
      2 * W + 2 * E := by
  dsimp only
  have hinj4 := (fw_four_family_pair_cells_injective f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols).1
  have hinj_bridge_pair : Function.Injective (fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc) := by
    intro a b h
    have h4 : fwFourFamilyPairCells f.hrect f.hseedrect f.hwide f.hoff f.hs choice
        f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
        (Sum.inl (Sum.inl (Sum.inl a))) =
      fwFourFamilyPairCells f.hrect f.hseedrect f.hwide f.hoff f.hs choice
        f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
        (Sum.inl (Sum.inl (Sum.inl b))) := h
    exact Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (hinj4 h4)))
  have hinj_wide_pair : Function.Injective (fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc) := by
    intro a b h
    have h4 : fwFourFamilyPairCells f.hrect f.hseedrect f.hwide f.hoff f.hs choice
        f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
        (Sum.inl (Sum.inr a)) =
      fwFourFamilyPairCells f.hrect f.hseedrect f.hwide f.hoff f.hs choice
        f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
        (Sum.inl (Sum.inr b)) := h
    exact Sum.inr.inj (Sum.inl.inj (hinj4 h4))
  obtain ⟨hinj_bridge, him_bridge⟩ := fw_double_cells_geometry
    (fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc) hinj_bridge_pair
  obtain ⟨hinj_wide, him_wide⟩ := fw_double_cells_geometry
    (fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc) hinj_wide_pair
  have hbw_main := fw_bridge_wide_diagonal_reference_sum_eq choice f oldReference hrect_fixed
    (fun z => z ∈ mainCells n) (fun z hz => Finset.mem_union_left _ hz)
  have hbw_anti := fw_bridge_wide_diagonal_reference_sum_eq choice f oldReference hrect_fixed
    (fun z => z ∈ antiCells n) (fun z hz => Finset.mem_union_right _ hz)
  dsimp only at hbw_main hbw_anti
  change Function.Injective (fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc) at hinj_bridge
  change Finset.univ.image (fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc) = _ at him_bridge
  change Function.Injective (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc) at hinj_wide
  change Finset.univ.image (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc) = _ at him_wide
  rw [← him_bridge, ← him_wide, hbw_main.1, hbw_anti.1, hbw_main.2, hbw_anti.2]
  let bridgeCells := fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
  let wideCells := fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
  have hwb (j : Fin 5) :
      (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight bridgeCells (fun c => c ∈ mainCells n) j b) = 12 ∧
      (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight bridgeCells (fun c => c ∈ antiCells n) j b) = 12 := by
    have h := fw_bridge_grouped_stage_diagonal_weight_sum f.hrect f.hseedrect f.hwide hgrowth f.hs hL
      otherG f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc
      (packedRectangleSupport f.hs choice)
      (LayerPacking.transposeCells (packedRectangleSupport f.hs choice ∪ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr)))
      f.hrows f.hcols j
    dsimp only at h
    rw [hchoice_eq] at h
    exact h
  have hww (j : Fin (3 * (n / 450))) :
      (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight wideCells (fun c => c ∈ mainCells n) j b) = 12 ∧
      (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight wideCells (fun c => c ∈ antiCells n) j b) = 12 := by
    have h := fw_wide_grouped_stage_diagonal_weight_sum f.hrect f.hseedrect f.hwide hgrowth f.hs hL
      otherG f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hwr f.hwc
      (packedRectangleSupport f.hs choice)
      (LayerPacking.transposeCells (packedRectangleSupport f.hs choice ∪ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr)))
      f.hrows f.hcols j
    dsimp only at h
    rw [hchoice_eq] at h
    exact h
  have hob (j : Fin 5) :
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
        physicalPairLineOrientation bridgeCells (fun c => c ∈ mainCells n) (j, b, p) * ((f.gapb j b : ℝ) / 2)) =
        -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n true, (f.gapb j b : ℝ) ∧
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
        physicalPairLineOrientation bridgeCells (fun c => c ∈ antiCells n) (j, b, p) * ((f.gapb j b : ℝ) / 2)) =
        -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n false, (f.gapb j b : ℝ) := by
    have h := fw_bridge_grouped_stage_diagonal_orientation_sum f.hrect f.hseedrect f.hwide hgrowth f.hs hL
      otherG f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc
      (packedRectangleSupport f.hs choice)
      (LayerPacking.transposeCells (packedRectangleSupport f.hs choice ∪ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr)))
      f.hrows f.hcols (fun b => (f.gapb j b : ℝ)) j
    dsimp only at h
    rw [hchoice_eq] at h
    exact h
  have how (j : Fin (3 * (n / 450))) :
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
        physicalPairLineOrientation wideCells (fun c => c ∈ mainCells n) (j, b, p) * ((f.gapw j b : ℝ) / 2)) =
        -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n true, (f.gapw j b : ℝ) ∧
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
        physicalPairLineOrientation wideCells (fun c => c ∈ antiCells n) (j, b, p) * ((f.gapw j b : ℝ) / 2)) =
        -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n false, (f.gapw j b : ℝ) := by
    have h := fw_wide_grouped_stage_diagonal_orientation_sum f.hrect f.hseedrect f.hwide hgrowth f.hs hL
      otherG f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hwr f.hwc
      (packedRectangleSupport f.hs choice)
      (LayerPacking.transposeCells (packedRectangleSupport f.hs choice ∪ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr)))
      f.hrows f.hcols (fun b => (f.gapw j b : ℝ)) j
    dsimp only at h
    rw [hchoice_eq] at h
    exact h
  have hdiff_b := double_block_diagonal_difference_of_equal_weights
    (fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc) hinj_bridge
    f.source f.ordered f.gapb f.hinvoiceb
    (fun j => (hwb j).1) (fun j => (hwb j).2) (fun j => (hob j).1) (fun j => (hob j).2)
  have hdiff_w := double_block_diagonal_difference_of_equal_weights
    (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc) hinj_wide
    f.source f.ordered f.gapw f.hinvoicew
    (fun j => (hww j).1) (fun j => (hww j).2) (fun j => (how j).1) (fun j => (how j).2)
  let lm : Fin ((n + n) + 2) := finSumFinEquiv (Sum.inr (0 : Fin 2))
  let la : Fin ((n + n) + 2) := finSumFinEquiv (Sum.inr (1 : Fin 2))
  have hline_m : (fun z => z ∈ physicalAllLineCells lm) = (fun z => z ∈ mainCells n) := by
    ext z; simp [lm, physicalAllLineCells]
  have hline_a : (fun z => z ∈ physicalAllLineCells la) = (fun z => z ∈ antiCells n) := by
    ext z; simp [la, physicalAllLineCells, show (1 : Fin 2) ≠ 0 by decide]
  have hbm := f.hBridgeScore lm
  have hba := f.hBridgeScore la
  have hwm := f.hWideScore lm
  have hwa := f.hWideScore la
  rw [hline_m] at hbm hwm
  rw [hline_a] at hba hwa
  have hbgap := fw_theta_bridge_signed_gap_contrast f
  rw [hdiff_b, hdiff_w]
  rw [abs_lt] at hbm hba hwm hwa hwgap
  rw [abs_le] at hbgap
  constructor
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith

private theorem cast_three_mul_div (n : ℕ) :
    ((3 * (n / 450) : ℕ) : ℝ) = 3 * ((n / 450 : ℕ) : ℝ) := by
  push_cast; rfl

private theorem fw_selected_choice_eq_bridge_seed_wide_growth {n : ℕ}
    (hnlo : 19485 ≤ n)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseedrect : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool) :
    fwBridgeSeedWideGrowthChoice hrect hseedrect hwide
      (fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)) otherChoice =
      fwSelectedThetaChoice hnlo otherChoice := by
  cases Subsingleton.elim hrect (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).1
  cases Subsingleton.elim hseedrect (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.1
  cases Subsingleton.elim hwide (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.1
  rfl

/-- On the reference square of the same supplied network, the bridge and wide
diagonal differences satisfy their first-band component bounds. -/
theorem fw_bridge_wide_reference_diagonal_differences {n : ℕ}
    (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n))
    (intermediate oldReference : Cell n ≃ Fin (n * n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice)
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (fresh : FWThetaFreshWideProjection f intermediate oldReference) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let bridge := fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
    let wide := fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
    let X : ℝ := poolMaximum n
    let k := ((n / 450 : ℕ) : ℝ)
    let B := X * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8))
    let W := X * (2 / 235 : ℝ) * Real.sqrt ((54 * k + 4) * Real.log (8 * (n : ℝ) + 8))
    let E := Real.sqrt ((3 / 2 : ℝ) * (3 * k) * ((64 / 235 : ℝ) * X)^2 * Real.log 16)
    |(∑ z ∈ (Finset.univ.image bridge).filter (fun z => z ∈ mainCells n), (entry oldReference z : ℝ)) -
      (∑ z ∈ (Finset.univ.image bridge).filter (fun z => z ∈ antiCells n), (entry oldReference z : ℝ))| <
      2 * B + (613256873 / 949132107 : ℝ) * X ∧
    |(∑ z ∈ (Finset.univ.image wide).filter (fun z => z ∈ mainCells n), (entry oldReference z : ℝ)) -
      (∑ z ∈ (Finset.univ.image wide).filter (fun z => z ∈ antiCells n), (entry oldReference z : ℝ))| <
      2 * W + 2 * E := by
  have hcontrast : |(1 / 2 : ℝ) * ((∑ j : Fin (3 * (n / 450)), ∑ b ∈ fwWideSignedGapSlots n true, (f.gapw j b : ℝ)) -
      ∑ j : Fin (3 * (n / 450)), ∑ b ∈ fwWideSignedGapSlots n false, (f.gapw j b : ℝ))| <
      2 * Real.sqrt ((3 / 2 : ℝ) * (3 * ((n / 450 : ℕ) : ℝ)) * ((64 / 235 : ℝ) * (poolMaximum n : ℝ))^2 * Real.log 16) := by
    rw [← cast_three_mul_div n]
    exact fresh.contrast
  exact fw_bridge_wide_diagonal_differences_of_choice
    (fwSelectedThetaChoice hnlo otherChoice) f oldReference net.rectangle_fixed
    (Nat.le_trans (by decide) f.hrect)
    (fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide))
    otherChoice
    (fw_selected_choice_eq_bridge_seed_wide_growth hnlo f.hrect f.hseedrect f.hwide otherChoice)
    hcontrast

end
end Sude
