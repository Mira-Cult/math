import Sude.FWGrowthRectangleChoice
import Sude.FWRectangleCapacity

/-! Active FW rectangle labels. This is index arithmetic only; it makes no
assertion about selected values or occupancy of unused-capacity labels. -/
namespace Sude
noncomputable section

/-- The exact label count for five bridge, sixteen seed, `3*(n/450)` wide,
and `P` actual growth stages. -/
def fwActiveRectangleCount (n P : ℕ) : ℕ :=
  24 * (5 + 16 + 3 * (n / 450) + P)

theorem fw_active_rectangle_count_le_capacity {n P : ℕ} (hP : P ≤ 238) :
    fwActiveRectangleCount n P ≤ fwJointRectangleCount n 254 := by
  simp only [fwActiveRectangleCount, fwJointRectangleCount]
  omega

/-- The initial interval of active labels within the 254-prefix capacity. -/
def fwActiveRectangleLabels (n P : ℕ) (hP : P ≤ 238) :
    Finset (Fin (fwJointRectangleCount n 254)) :=
  Finset.univ.image (Fin.castLE (fw_active_rectangle_count_le_capacity hP))

/-- Capacity labels beyond the active interval; no claim about their values. -/
def fwSpareRectangleLabels (n P : ℕ) (hP : P ≤ 238) :
    Finset (Fin (fwJointRectangleCount n 254)) :=
  Finset.univ \ fwActiveRectangleLabels n P hP

theorem fw_active_rectangle_label_mem_iff (n P : ℕ) (hP : P ≤ 238)
    (x : Fin (fwJointRectangleCount n 254)) :
    x ∈ fwActiveRectangleLabels n P hP ↔ x.val < fwActiveRectangleCount n P := by
  classical
  simp only [fwActiveRectangleLabels, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    have h := congrArg Fin.val hi
    simpa using h ▸ i.isLt
  · intro hx
    exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩

theorem fw_spare_rectangle_label_mem_iff (n P : ℕ) (hP : P ≤ 238)
    (x : Fin (fwJointRectangleCount n 254)) :
    x ∈ fwSpareRectangleLabels n P hP ↔ fwActiveRectangleCount n P ≤ x.val := by
  classical
  simp [fwSpareRectangleLabels, fw_active_rectangle_label_mem_iff]

theorem fw_active_rectangle_label_count (n P : ℕ) (hP : P ≤ 238) :
    (fwActiveRectangleLabels n P hP).card = 24 * (5 + 16 + 3 * (n / 450) + P) := by
  classical
  unfold fwActiveRectangleLabels
  rw [Finset.card_image_of_injective _ (Fin.castLE_injective _)]
  rw [Finset.card_univ, Fintype.card_fin]
  simp [fwActiveRectangleCount]

theorem fw_spare_rectangle_label_count (n P : ℕ) (hP : P ≤ 238) :
    (fwSpareRectangleLabels n P hP).card = 24 * (238 - P) := by
  classical
  unfold fwSpareRectangleLabels
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    fw_active_rectangle_label_count]
  simp only [fwJointRectangleCount]
  omega

/-- The active interval is the union of the four consecutive bridge, seed,
wide and actual-growth label images. -/
theorem fw_active_labels_eq_family_union (n P : ℕ) (hP : P ≤ 238) :
    let L := fwJointRectangleCount n 254
    let hrect : 5 * (4 * 6) ≤ L := by dsimp [L, fwJointRectangleCount]; omega
    let hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L := by dsimp [L, fwJointRectangleCount]; omega
    let hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L := by
      dsimp [L, fwJointRectangleCount]; omega
    let hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L := by
      dsimp [L, fwJointRectangleCount]; omega
    fwActiveRectangleLabels n P hP =
      (Finset.univ.image (bridgeDiagonalRectangle (J := 5) (d := 6) hrect)) ∪
      (Finset.univ.image (fwSeedRectangle hseed)) ∪
      (Finset.univ.image (fwWideRectangle (J := 3 * (n / 450)) hwide)) ∪
      (Finset.univ.image (btGrowingOffsetRectangle (P := P) (d := 6)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff)) := by
  classical
  dsimp only
  ext x
  simp only [fwActiveRectangleLabels, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    have hx : x.val < fwActiveRectangleCount n P := by
      have h := congrArg Fin.val hi
      simpa using h ▸ i.isLt
    simp only [fwActiveRectangleCount] at hx
    by_cases hbridge : x.val < 5 * (4 * 6)
    · left; left; left
      refine ⟨⟨x.val, hbridge⟩, ?_⟩
      apply Fin.ext
      simp [bridgeDiagonalRectangle]
    · by_cases hseed : x.val < 5 * (4 * 6) + 16 * (4 * 6)
      · left; left; right
        refine ⟨⟨x.val - 5 * (4 * 6), by omega⟩, ?_⟩
        apply Fin.ext
        simp only [fwSeedRectangle]
        omega
      · by_cases hwide : x.val < 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
        · left; right
          refine ⟨⟨x.val - (5 * (4 * 6) + 16 * (4 * 6)), by omega⟩, ?_⟩
          apply Fin.ext
          simp only [fwWideRectangle]
          omega
        · right
          refine ⟨⟨x.val - (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)), by omega⟩, ?_⟩
          apply Fin.ext
          simp only [btGrowingOffsetRectangle]
          omega
  · intro h
    have hx : x.val < fwActiveRectangleCount n P := by
      rcases h with (((⟨i, hi⟩ | ⟨i, hi⟩) | ⟨i, hi⟩) | ⟨i, hi⟩)
      all_goals have he := congrArg Fin.val hi
      all_goals have hlt := i.isLt
      all_goals simp only [fwActiveRectangleCount, bridgeDiagonalRectangle, Fin.val_castLE,
        fwSeedRectangle, fwWideRectangle, btGrowingOffsetRectangle] at he ⊢
      all_goals omega
    refine ⟨⟨x.val, hx⟩, ?_⟩
    apply Fin.ext
    rfl

end
end Sude
