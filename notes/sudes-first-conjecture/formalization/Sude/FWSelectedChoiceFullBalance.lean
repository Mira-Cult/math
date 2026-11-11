import Sude.FWSelectedThetaWitness

/-! All actual capacity labels have a balanced selected diagonal choice.
This is label arithmetic only: no value, square, or prime claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- The total number of 24-rectangle blocks in the selected capacity. -/
def fwSelectedChoiceBlockCount (n : ℕ) : ℕ := 5 + 16 + 3*(n/450) + 238

/-- The physical label at a global capacity block and offset. -/
def fwSelectedFullBlockLabel (n : ℕ)
    (j : Fin (fwSelectedChoiceBlockCount n)) (r : Fin (4*6)) :
    Fin (fwJointRectangleCount n 254) :=
  ⟨24*j.val + r.val, by
    have hj := j.isLt
    have hr := r.isLt
    dsimp [fwSelectedChoiceBlockCount, fwJointRectangleCount] at *
    omega⟩

/-- The selected choice on every block, including all latent growth blocks. -/
theorem fw_selected_choice_by_block {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (j : Fin (fwSelectedChoiceBlockCount n)) (r : Fin (4*6)) :
    fwSelectedThetaChoice hnlo otherChoice
      (fwSelectedFullBlockLabel n j r) =
      decide (r.val < 12) := by
  let hrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).1
  let hseed := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.1
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  by_cases hb : j.val < 5
  · let t : Fin 5 := ⟨j.val,hb⟩
    have he : bridgeDiagonalRectangle hrect (finProdFinEquiv (t,r)) =
        fwSelectedFullBlockLabel n j r := by
      apply Fin.ext
      simp [bridgeDiagonalRectangle, finProdFinEquiv, fwSelectedFullBlockLabel, t] <;> omega
    have h := fwBridgeSeedWideGrowthChoice_bridge hrect hseed hwide hmax otherChoice t r
    rw [he] at h
    simpa only [fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
      fwBridgeSeedWideRectangleChoice, hrect, hseed, hwide, hmax] using h
  · by_cases hs : j.val < 5+16
    · let t : Fin 16 := ⟨j.val-5, by omega⟩
      have he : fwSeedRectangle hseed (finProdFinEquiv (t,r)) =
          fwSelectedFullBlockLabel n j r := by
        apply Fin.ext
        simp [fwSeedRectangle, finProdFinEquiv, fwSelectedFullBlockLabel, t] <;> omega
      have h := fwBridgeSeedWideGrowthChoice_seed hrect hseed hwide hmax otherChoice t r
      rw [he] at h
      simpa only [fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
        fwBridgeSeedWideRectangleChoice, hrect, hseed, hwide, hmax] using h
    · by_cases hw : j.val < 5+16+3*(n/450)
      · let t : Fin (3*(n/450)) := ⟨j.val-(5+16), by omega⟩
        have he : fwWideRectangle hwide (finProdFinEquiv (t,r)) =
            fwSelectedFullBlockLabel n j r := by
          apply Fin.ext
          simp [fwWideRectangle, finProdFinEquiv, fwSelectedFullBlockLabel, t] <;> omega
        have h := fwBridgeSeedWideGrowthChoice_wide hrect hseed hwide hmax otherChoice t r
        rw [he] at h
        simpa only [fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
          fwBridgeSeedWideRectangleChoice, hrect, hseed, hwide, hmax] using h
      · let t : Fin 238 := ⟨j.val-(5+16+3*(n/450)), by
          have hj := j.isLt; dsimp [fwSelectedChoiceBlockCount] at hj; omega⟩
        have he : fwGrowthRectangle hmax (finProdFinEquiv (t,r)) =
            fwSelectedFullBlockLabel n j r := by
          apply Fin.ext
          simp [fwGrowthRectangle, finProdFinEquiv, fwSelectedFullBlockLabel, t] <;> omega
        have h := fwBridgeSeedWideGrowthChoice_growth hrect hseed hwide hmax otherChoice t r
        rw [he] at h
        simpa only [fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
          fwBridgeSeedWideRectangleChoice, hrect, hseed, hwide, hmax] using h

/-- The chosen twelve labels on a given side in each capacity block. -/
def fwSelectedFullSideLabel (n : ℕ) (side : Bool)
    (x : Fin (fwSelectedChoiceBlockCount n) × Fin 12) : Fin (fwJointRectangleCount n 254) :=
  ⟨24*x.1.val + (if side then 0 else 12) + x.2.val, by
    have hj := x.1.isLt; have hr := x.2.isLt
    dsimp [fwSelectedChoiceBlockCount, fwJointRectangleCount] at *
    cases side <;> simp_all <;> omega⟩

/-- Exactly twelve labels per capacity block lie on each selected side. -/
theorem fw_selected_choice_full_balance {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool) (side : Bool) :
    ((Finset.univ : Finset (Fin (fwJointRectangleCount n 254))).filter
      (fun i => fwSelectedThetaChoice hnlo otherChoice i = side)).card =
      12 * fwSelectedChoiceBlockCount n := by
  classical
  let label := fwSelectedFullSideLabel n side
  have hinj : Function.Injective label := by
    intro x y h
    have hv := congrArg Fin.val h
    apply Prod.ext <;> apply Fin.ext
    · dsimp [label, fwSelectedFullSideLabel] at hv
      have hx := x.2.isLt; have hy := y.2.isLt
      cases side <;> simp_all <;> omega
    · dsimp [label, fwSelectedFullSideLabel] at hv
      have hx := x.2.isLt; have hy := y.2.isLt
      cases side <;> simp_all <;> omega
  have hmem (x : Fin (fwSelectedChoiceBlockCount n) × Fin 12) :
      label x ∈ (Finset.univ : Finset (Fin (fwJointRectangleCount n 254))).filter
        (fun i => fwSelectedThetaChoice hnlo otherChoice i = side) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    let r : Fin (4*6) := if side then ⟨x.2.val, by have h := x.2.isLt; omega⟩
      else ⟨12+x.2.val, by have h := x.2.isLt; omega⟩
    have he : label x = fwSelectedFullBlockLabel n x.1 r := by
      apply Fin.ext
      cases side <;> simp [label, fwSelectedFullSideLabel, fwSelectedFullBlockLabel, r, Nat.add_assoc]
    rw [he, fw_selected_choice_by_block]
    cases side <;> simp [r] <;> omega
  have hsurj (i : Fin (fwJointRectangleCount n 254))
      (hi : i ∈ (Finset.univ : Finset (Fin (fwJointRectangleCount n 254))).filter
        (fun i => fwSelectedThetaChoice hnlo otherChoice i = side)) : ∃ x, label x = i := by
    let j : Fin (fwSelectedChoiceBlockCount n) := ⟨i.val/24, by
      have hi := i.isLt; dsimp [fwSelectedChoiceBlockCount, fwJointRectangleCount] at *; omega⟩
    let r : Fin (4*6) := ⟨i.val%24, by omega⟩
    have he : fwSelectedFullBlockLabel n j r = i := by
      apply Fin.ext
      dsimp [fwSelectedFullBlockLabel, j,r]
      omega
    have hc : decide (r.val < 12) = side := by
      rw [← fw_selected_choice_by_block hnlo otherChoice j r, he]
      exact (Finset.mem_filter.mp hi).2
    cases side with
    | false =>
      have hr : 12 ≤ r.val := by simpa using hc
      let x : Fin (fwSelectedChoiceBlockCount n) × Fin 12 := (j, ⟨r.val-12, by have := r.isLt; omega⟩)
      refine ⟨x, ?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val he
      change 24*j.val + r.val = i.val at hv
      dsimp [label, fwSelectedFullSideLabel, x]
      omega
    | true =>
      have hr : r.val < 12 := by simpa using hc
      let x : Fin (fwSelectedChoiceBlockCount n) × Fin 12 := (j, ⟨r.val,hr⟩)
      refine ⟨x, ?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val he
      change 24*j.val + r.val = i.val at hv
      dsimp [label, fwSelectedFullSideLabel, x]
      omega
  have hset : (Finset.univ : Finset (Fin (fwJointRectangleCount n 254))).filter
      (fun i => fwSelectedThetaChoice hnlo otherChoice i = side) = Finset.univ.image label := by
    ext i
    constructor
    · intro hi
      obtain ⟨x,rfl⟩ := hsurj i hi
      exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    · intro hi
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
      exact hmem x
  rw [hset, Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  omega

end
end Sude
