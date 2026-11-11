import Sude.DoubleBlockPhysicalMidpointPartition
import Sude.LayerTranspose

/-! Transposition preserves grouped midpoint data and exchanges physical rows
and columns. Boolean sides and signed gaps are unchanged. -/
namespace Sude
noncomputable section

@[simp] theorem double_block_transpose_entry {n : ℕ}
    (a : Cell n ≃ Fin (n*n)) (z : Cell n) :
    entry (LayerPacking.transposePlacement a) z.swap = entry a z := by
  rcases z with ⟨i,j⟩
  rfl

/-- Transpose both the cell map and the predicate; endpoint sides stay fixed. -/
theorem physical_pair_line_weight_transpose {n : ℕ} {α : Type*}
    (cells : α × Bool → Cell n) (line : Cell n → Prop) (i : α) :
    physicalPairLineWeight (fun x => (cells x).swap) (fun z => line z.swap) i =
      physicalPairLineWeight cells line i := by
  classical
  simp [physicalPairLineWeight]

theorem physical_pair_line_orientation_transpose {n : ℕ} {α : Type*}
    (cells : α × Bool → Cell n) (line : Cell n → Prop) (i : α) :
    physicalPairLineOrientation (fun x => (cells x).swap) (fun z => line z.swap) i =
      physicalPairLineOrientation cells line i := by
  classical
  simp [physicalPairLineOrientation]

theorem double_block_pair_midpoint_transpose {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (a : Cell n ≃ Fin (n*n)) (j : Fin P) (b : Fin B) (p : Fin 2) :
    doubleBlockPairMidpoint (fun x => (cells x).swap) (LayerPacking.transposePlacement a) j b p =
      doubleBlockPairMidpoint cells a j b p := by
  simp [doubleBlockPairMidpoint]

theorem double_block_midpoint_transpose {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (a : Cell n ≃ Fin (n*n)) (j : Fin P) (b : Fin B) :
    doubleBlockMidpoint (fun x => (cells x).swap) (LayerPacking.transposePlacement a) j b =
      doubleBlockMidpoint cells a j b := by
  simp [doubleBlockMidpoint, double_block_pair_midpoint_transpose]

theorem double_stage_midpoint_mean_transpose {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (a : Cell n ≃ Fin (n*n)) (j : Fin P) :
    doubleStageMidpointMean (fun x => (cells x).swap) (LayerPacking.transposePlacement a) j =
      doubleStageMidpointMean cells a j := by
  simp [doubleStageMidpointMean, double_block_midpoint_transpose]

theorem double_block_line_weight_transpose {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (j : Fin P) (b : Fin B) :
    doubleBlockLineWeight (fun x => (cells x).swap) (fun z => line z.swap) j b =
      doubleBlockLineWeight cells line j b := by
  simp [doubleBlockLineWeight, physical_pair_line_weight_transpose]

theorem double_block_actual_centered_score_transpose {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old new : Cell n ≃ Fin (n*n)) :
    doubleBlockActualCenteredScore (fun x => (cells x).swap) (fun z => line z.swap)
        (LayerPacking.transposePlacement old) (LayerPacking.transposePlacement new) =
      doubleBlockActualCenteredScore cells line old new := by
  simp [doubleBlockActualCenteredScore, physical_pair_line_weight_transpose,
    double_block_pair_midpoint_transpose, double_block_line_weight_transpose,
    double_stage_midpoint_mean_transpose]

theorem physical_pair_gap_transpose {n : ℕ} {α : Type*}
    (cells : α × Bool → Cell n) (a : Cell n ≃ Fin (n*n)) (i : α) :
    (entry (LayerPacking.transposePlacement a) (cells (i,true)).swap : ℝ) -
        entry (LayerPacking.transposePlacement a) (cells (i,false)).swap =
      (entry a (cells (i,true)) : ℝ) - entry a (cells (i,false)) := by
  simp

/-- The transposed row complement is exactly the original column complement;
no injectivity of the supplied cell map is required. -/
theorem physical_column_complement_transpose {n : ℕ} {α : Type*} [Fintype α]
    (cells : α → Cell n) (a : Cell n ≃ Fin (n*n)) (c : Fin n) :
    let A := Finset.univ.image cells
    let col := (Finset.univ : Finset (Fin n)).image (fun r => (r,c))
    let rowT := (Finset.univ : Finset (Fin n)).image (fun r => (c,r))
    (∑ z ∈ rowT \ Finset.univ.image (fun x => (cells x).swap),
      (entry (LayerPacking.transposePlacement a) z : ℝ)) =
    ∑ z ∈ col \ A, (entry a z : ℝ) := by
  classical
  dsimp only
  have hswap : Function.Injective (Prod.swap : Cell n → Cell n) := by
    intro x y h
    simpa using congrArg Prod.swap h
  have hsets :
      ((Finset.univ : Finset (Fin n)).image (fun r => (c,r)) \ 
        Finset.univ.image (fun x => (cells x).swap)) =
      (((Finset.univ : Finset (Fin n)).image (fun r => (r,c)) \ 
        Finset.univ.image cells).image Prod.swap) := by
    rw [Finset.image_sdiff _ _ hswap]
    simp only [Finset.image_image, Function.comp_def, Prod.swap_prod_mk]
  rw [hsets, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z _
    cases z
    rfl
  · intro x _ y _ h
    exact hswap h

end
end Sude
