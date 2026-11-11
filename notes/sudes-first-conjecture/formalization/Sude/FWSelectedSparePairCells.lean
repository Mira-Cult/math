import Sude.FWSelectedSpareChoiceCount
import Sude.ActiveRectangleDiagonalGeometry
import Sude.SpareRectangleLineSeparation

/-! The designated main and antidiagonal cells of each latent spare stage.
This is geometry only; no value balance, permutation, CY or flow claim. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- Pair each spare stage/slot's designated cells on the two diagonals. -/
def fwSelectedSparePairCell {n P : ℕ} (hP : P ≤ 238) (hnlo : 19485 ≤ n)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (x : (Fin (238-P) × Fin 12) × Bool) : Cell n :=
  packedRectangleCorner hs (fwSelectedThetaChoice hnlo otherChoice)
    (fwSelectedSpareSideLabel hP x.2 x.1, 0)

theorem fw_selected_spare_side_choice {n P : ℕ} (hP : P ≤ 238) (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (side : Bool) (x : Fin (238-P) × Fin 12) :
    fwSelectedThetaChoice hnlo otherChoice (fwSelectedSpareSideLabel hP side x) = side := by
  let hrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).1
  let hseed := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.1
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  let j : Fin 238 := ⟨P + x.1.val, by have h := x.1.isLt; omega⟩
  let r : Fin (4*6) := if side then ⟨x.2.val, by have h := x.2.isLt; omega⟩
    else ⟨12+x.2.val, by have h := x.2.isLt; omega⟩
  have h := fwBridgeSeedWideGrowthChoice_growth hrect hseed hwide hmax otherChoice j r
  change fwSelectedThetaChoice hnlo otherChoice (fwGrowthRectangle hmax (finProdFinEquiv (j,r))) = side
  rw [show fwSelectedThetaChoice hnlo otherChoice (fwGrowthRectangle hmax (finProdFinEquiv (j,r))) =
      decide (r.val < 12) by simpa only [fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
        fwBridgeSeedWideRectangleChoice, hrect, hseed, hwide, hmax] using h]
  cases side <;> simp [r]

theorem fw_selected_spare_side_mem {n P : ℕ} (hP : P ≤ 238) (side : Bool)
    (x : Fin (238-P) × Fin 12) :
    fwSelectedSpareSideLabel (n := n) hP side x ∈ fwSpareRectangleLabels n P hP := by
  apply (fw_spare_rectangle_label_mem_iff n P hP _).2
  dsimp [fwSelectedSpareSideLabel, fwGrowthRectangle, fwActiveRectangleCount, finProdFinEquiv]
  split <;> simp_all <;> omega

theorem fw_selected_spare_side_injective {n P : ℕ} (hP : P ≤ 238) :
    Function.Injective (fun x : (Fin (238-P) × Fin 12) × Bool =>
      fwSelectedSpareSideLabel (n := n) hP x.2 x.1) := by
  intro ⟨⟨i,r⟩,b⟩ ⟨⟨j,s⟩,c⟩ h
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  have hp := finProdFinEquiv.injective ((fwGrowthRectangle_injective hmax) h)
  have hj := congrArg (fun q => q.1.val) hp
  have hr := congrArg (fun q => q.2.val) hp
  dsimp [fwSelectedSpareSideLabel] at hj hr
  have hij : i = j := by apply Fin.ext; omega
  have hbc : b = c := by cases b <;> cases c <;> simp_all <;> omega
  have hrs : r = s := by cases b <;> cases c <;> simp_all <;> apply Fin.ext <;> omega
  subst j; subst c; subst s; rfl

theorem fw_selected_spare_pair_cell_injective {n P : ℕ} (hP : P ≤ 238) (hnlo : 19485 ≤ n)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool) :
    Function.Injective (fwSelectedSparePairCell hP hnlo hs otherChoice) := by
  intro x y h
  apply fw_selected_spare_side_injective hP
  exact congrArg Prod.fst (packedRectangleCorner_injective hs _ h)

theorem fw_selected_spare_pair_cell_diagonal {n P : ℕ} (hP : P ≤ 238) (hnlo : 19485 ≤ n)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (x : Fin (238-P) × Fin 12) :
    fwSelectedSparePairCell hP hnlo hs otherChoice (x,true) ∈ mainCells n ∧
    fwSelectedSparePairCell hP hnlo hs otherChoice (x,false) ∈ antiCells n := by
  constructor
  · simpa [fwSelectedSparePairCell, packedRectangleCorner] using
      ((RectanglePacking.designated_corner_geometry hs (fwSelectedThetaChoice hnlo otherChoice)
        (fwSelectedSpareSideLabel hP true x)).1 (fw_selected_spare_side_choice hP hnlo otherChoice true x)).1
  · simpa [fwSelectedSparePairCell, packedRectangleCorner] using
      ((RectanglePacking.designated_corner_geometry hs (fwSelectedThetaChoice hnlo otherChoice)
        (fwSelectedSpareSideLabel hP false x)).2 (fw_selected_spare_side_choice hP hnlo otherChoice false x)).1

theorem fw_selected_spare_pair_line_injective {n P : ℕ} (hP : P ≤ 238) (hnlo : 19485 ≤ n)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (x y : (Fin (238-P) × Fin 12) × Bool) :
    ((fwSelectedSparePairCell hP hnlo hs otherChoice x).1 =
      (fwSelectedSparePairCell hP hnlo hs otherChoice y).1 → x = y) ∧
    ((fwSelectedSparePairCell hP hnlo hs otherChoice x).2 =
      (fwSelectedSparePairCell hP hnlo hs otherChoice y).2 → x = y) := by
  constructor <;> intro h <;> apply fw_selected_spare_side_injective hP
  · exact packedCorner_row_label hs _ _ _ 0 0 h
  · exact packedCorner_column_label hs _ _ _ 0 0 h

/-- Every spare label on a side is represented exactly once. -/
theorem fw_selected_spare_side_labels {n P : ℕ} (hP : P ≤ 238) (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool) (side : Bool) :
    (Finset.univ : Finset (Fin (238-P) × Fin 12)).image
        (fwSelectedSpareSideLabel (n := n) hP side) =
      (fwSpareRectangleLabels n P hP).filter
        (fun i => fwSelectedThetaChoice hnlo otherChoice i = side) := by
  classical
  have hinj : Function.Injective (fwSelectedSpareSideLabel (n := n) hP side) := by
    intro x y h
    have := fw_selected_spare_side_injective (n := n) hP (show
      fwSelectedSpareSideLabel hP ((x,side) : (Fin (238-P) × Fin 12) × Bool).2 ((x,side) : (Fin (238-P) × Fin 12) × Bool).1 =
      fwSelectedSpareSideLabel hP ((y,side) : (Fin (238-P) × Fin 12) × Bool).2 ((y,side) : (Fin (238-P) × Fin 12) × Bool).1 from h)
    exact congrArg Prod.fst this
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨fw_selected_spare_side_mem hP side x,
      fw_selected_spare_side_choice hP hnlo otherChoice side x⟩
  · rw [Finset.card_image_of_injective _ hinj, fw_selected_spare_choice_count hnlo hP otherChoice side]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    omega

/-- The paired cells exhaust precisely the spare cells on each diagonal. -/
theorem fw_selected_spare_pair_cell_images {n P : ℕ} (hP : P ≤ 238) (hnlo : 19485 ≤ n)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (Finset.univ : Finset (Fin (238-P) × Fin 12)).image
        (fun x => fwSelectedSparePairCell hP hnlo hs otherChoice (x,true)) = spare ∩ mainCells n ∧
    (Finset.univ : Finset (Fin (238-P) × Fin 12)).image
        (fun x => fwSelectedSparePairCell hP hnlo hs otherChoice (x,false)) = spare ∩ antiCells n := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  have hL : 3 ≤ fwJointRectangleCount n 254 := by simp [fwJointRectangleCount]; omega
  have hsp := (fw_spare_rectangle_line_separation hP hs choice).2.2.2
  constructor
  · rw [hsp, active_rectangle_main_cells hs hL choice,
      ← fw_selected_spare_side_labels hP hnlo otherChoice true, Finset.image_image]
    rfl
  · rw [hsp, active_rectangle_anti_cells hs hL choice,
      ← fw_selected_spare_side_labels hP hnlo otherChoice false, Finset.image_image]
    rfl

end
end Sude
