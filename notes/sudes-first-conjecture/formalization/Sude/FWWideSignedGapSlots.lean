import Sude.FWControllerStageReindex

/-! The two disjoint sets of physical destination blocks corresponding to
one wide stage's 12 main and 12 anti rectangles. No probability, gap-value,
or selected-witness conclusion is asserted. -/
namespace Sude
noncomputable section

/-- The first twelve rectangle indices are assigned to the main side and the
second twelve to the anti side by the balanced rectangle choice. -/
def fwWideSignedGapRectangle (side : Bool) (r : Fin 12) : Fin (4 * 6) :=
  ⟨if side then r.val else 12 + r.val, by have hr := r.isLt; split_ifs <;> omega⟩

/-- The rectangle index is also its destination double-block index. -/
def fwWideSignedGapSlot (n : ℕ) (side : Bool) (r : Fin 12) : Fin (3 * (n + 8)) :=
  Fin.castLE (by omega : 4 * 6 ≤ 3 * (n + 8)) (fwWideSignedGapRectangle side r)

/-- The twelve destination blocks for one diagonal side of one wide stage. -/
def fwWideSignedGapSlots (n : ℕ) (side : Bool) : Finset (Fin (3 * (n + 8))) :=
  Finset.univ.image (fwWideSignedGapSlot n side)

/-- The twelve rectangle-to-block maps are injective on either side. -/
theorem fw_wide_signed_gap_slot_injective (n : ℕ) (side : Bool) :
    Function.Injective (fwWideSignedGapSlot n side) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  cases side <;> simp [fwWideSignedGapSlot, fwWideSignedGapRectangle] at hv ⊢ <;> omega

/-- Each side consists of exactly twelve distinct destination blocks, and the
main and anti sets are disjoint. -/
theorem fw_wide_signed_gap_slots_card_disjoint (n : ℕ) :
    (fwWideSignedGapSlots n true).card = 12 ∧
    (fwWideSignedGapSlots n false).card = 12 ∧
    Disjoint (fwWideSignedGapSlots n true) (fwWideSignedGapSlots n false) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [fwWideSignedGapSlots, Finset.card_image_of_injective _ (fw_wide_signed_gap_slot_injective n true)]
    simp
  · rw [fwWideSignedGapSlots, Finset.card_image_of_injective _ (fw_wide_signed_gap_slot_injective n false)]
    simp
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    have hv := congrArg Fin.val (ha.trans hb.symm)
    simp [fwWideSignedGapSlot, fwWideSignedGapRectangle] at hv
    have halt := a.isLt
    omega

/-- The same destination block index is used for both pairs of a rectangle;
it is not a pair of rectangle indices sharing one block. -/
theorem fw_wide_signed_gap_controller_index (n : ℕ) (side : Bool)
    (r : Fin 12) (pair : Fin 2) :
    fwPrefixToControllerPair n
      (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega)
        (fwWideSignedGapRectangle side r, pair)) =
      Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
        (finProdFinEquiv (fwWideSignedGapSlot n side r, pair)) := by
  exact fwPrefixToControllerPair_diagonal n (fwWideSignedGapRectangle side r) pair

end
end Sude
