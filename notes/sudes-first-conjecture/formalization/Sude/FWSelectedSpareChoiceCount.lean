import Sude.FWSelectedThetaWitness
import Sude.FWActiveRectangleLabels

/-! The selected choice balances the latent, not-yet-realized growth rectangle
labels. No claim about their entries or selected growth stages is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

/-- A canonical label on either side in a latent growth stage. -/
def fwSelectedSpareSideLabel {n P : ℕ} (hP : P ≤ 238) (side : Bool)
    (x : Fin (238-P) × Fin 12) : Fin (fwJointRectangleCount n 254) :=
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  let j : Fin 238 := ⟨P + x.1.val, by have h := x.1.isLt; omega⟩
  let r : Fin (4*6) := if side then ⟨x.2.val, by have h := x.2.isLt; omega⟩
    else ⟨12 + x.2.val, by have h := x.2.isLt; omega⟩
  fwGrowthRectangle hmax (finProdFinEquiv (j,r))

/-- Each half of every latent stage has twelve labels on its selected side. -/
theorem fw_selected_spare_choice_count {n P : ℕ} (hnlo : 19485 ≤ n) (hP : P ≤ 238)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool) (side : Bool) :
    ((fwSpareRectangleLabels n P hP).filter (fun i => fwSelectedThetaChoice hnlo otherChoice i = side)).card =
      12 * (238-P) := by
  classical
  let hrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).1
  let hseed := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.1
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  let label := fwSelectedSpareSideLabel (n := n) hP side
  have hchoice (j : Fin 238) (r : Fin (4*6)) :
      fwSelectedThetaChoice hnlo otherChoice (fwGrowthRectangle hmax (finProdFinEquiv (j,r))) =
        decide (r.val < 12) := by
    have h := fwBridgeSeedWideGrowthChoice_growth hrect hseed hwide hmax otherChoice j r
    simpa only [fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
      fwBridgeSeedWideRectangleChoice, hrect, hseed, hwide, hmax] using h
  have hinj : Function.Injective label := by
    intro x y h
    have hp := finProdFinEquiv.injective ((fwGrowthRectangle_injective hmax) h)
    have hj := congrArg (fun q => q.1.val) hp
    have hr := congrArg (fun q => q.2.val) hp
    apply Prod.ext <;> apply Fin.ext
    · simp only [label, fwSelectedSpareSideLabel] at hj
      omega
    · cases side <;> simp only [label, fwSelectedSpareSideLabel, Bool.false_eq_true,
        ↓reduceIte] at hr <;> omega
  have hmem (x : Fin (238-P) × Fin 12) :
      label x ∈ (fwSpareRectangleLabels n P hP).filter (fun i => fwSelectedThetaChoice hnlo otherChoice i = side) := by
    apply Finset.mem_filter.mpr
    constructor
    · apply (fw_spare_rectangle_label_mem_iff n P hP _).2
      dsimp [label, fwSelectedSpareSideLabel, fwGrowthRectangle, fwActiveRectangleCount, finProdFinEquiv]
      split <;> simp_all <;> omega
    · dsimp only [label, fwSelectedSpareSideLabel]
      rw [hchoice]
      cases side <;> simp <;> omega
  have hsurj (i : Fin (fwJointRectangleCount n 254))
      (hi : i ∈ (fwSpareRectangleLabels n P hP).filter (fun i => fwSelectedThetaChoice hnlo otherChoice i = side)) :
      ∃ x, label x = i := by
    have hs := (fw_spare_rectangle_label_mem_iff n P hP i).1 (Finset.mem_filter.mp hi).1
    have hl := i.isLt
    let base := 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)
    have hlo : base + 24*P ≤ i.val := by dsimp [base, fwActiveRectangleCount] at *; omega
    have hhi : i.val < base + 24*238 := by dsimp [base, fwJointRectangleCount] at *; omega
    let q := i.val - base
    let j : Fin 238 := ⟨q / 24, by dsimp [q] at *; omega⟩
    let r : Fin (4*6) := ⟨q % 24, by omega⟩
    have hji : P ≤ j.val := by dsimp [j,q] at *; omega
    have heq : fwGrowthRectangle hmax (finProdFinEquiv (j,r)) = i := by
      apply Fin.ext
      dsimp [fwGrowthRectangle, finProdFinEquiv, j, r, q, base]
      omega
    have hc : decide (r.val < 12) = side := by
      rw [← hchoice j r, heq]
      exact (Finset.mem_filter.mp hi).2
    cases side with
    | false =>
      have hr : 12 ≤ r.val := by simpa using hc
      let x : Fin (238-P) × Fin 12 := (⟨j.val-P, by have := j.isLt; omega⟩,
        ⟨r.val-12, by have := r.isLt; omega⟩)
      refine ⟨x, ?_⟩
      apply Fin.ext
      have he := congrArg Fin.val heq
      simp only [label, fwSelectedSpareSideLabel, Bool.false_eq_true, ↓reduceIte,
        fwGrowthRectangle, finProdFinEquiv] at *
      dsimp [x] at *
      omega
    | true =>
      have hr : r.val < 12 := by simpa using hc
      let x : Fin (238-P) × Fin 12 := (⟨j.val-P, by have := j.isLt; omega⟩, ⟨r.val, hr⟩)
      refine ⟨x, ?_⟩
      apply Fin.ext
      have he := congrArg Fin.val heq
      simp only [label, fwSelectedSpareSideLabel, ↓reduceIte,
        fwGrowthRectangle, finProdFinEquiv] at *
      dsimp [x] at *
      omega
  have hset : (fwSpareRectangleLabels n P hP).filter (fun i => fwSelectedThetaChoice hnlo otherChoice i = side) =
      Finset.univ.image label := by
    ext i
    constructor
    · intro hi
      obtain ⟨x, rfl⟩ := hsurj i hi
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    · intro hi
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
      exact hmem x
  rw [hset, Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  omega

end
end Sude
