import Sude.RectanglePairInvoice

/-! Restrict the rectangle invoice to the actual selected prefix slots. -/
namespace Sude
noncomputable section

/-- The actual stage and rectangle labels inject into the packed rectangles. -/
def prefixRectanglePairSlot {P d L : ℕ} (hrect : P * (4 * d) ≤ L) :
    ((Fin P × Fin (4 * d)) × Fin 2) → (Fin L × Fin 2) :=
  fun x => (Fin.castLE hrect (finProdFinEquiv x.1), x.2)

theorem prefixRectanglePairSlot_injective {P d L : ℕ} (hrect : P * (4 * d) ≤ L) :
    Function.Injective (prefixRectanglePairSlot hrect) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have hi : i = j := finProdFinEquiv.injective
    (Fin.castLE_injective hrect (congrArg Prod.fst h))
  have hp : p = q := congrArg Prod.snd h
  exact Prod.ext hi hp

/-- The selected prefix rectangle slots inherit the physical row invoice. -/
theorem prefixRectangle_row_pair_invoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    (∑ x, (rectanglePairWeight hs choice (fun c => c.1 = r)
      (prefixRectanglePairSlot hrect x)) ^ 2) ≤ 4 := by
  classical
  let w : Fin L × Fin 2 → ℝ := rectanglePairWeight hs choice (fun c => c.1 = r)
  let e := prefixRectanglePairSlot hrect
  have hsub : Finset.univ.image e ⊆ (Finset.univ : Finset (Fin L × Fin 2)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x => (w x) ^ 2) (by intro x hx hx'; exact sq_nonneg (w x))
  rw [Finset.sum_image (by intro x _ y _ h; exact prefixRectanglePairSlot_injective hrect h)] at hsum
  exact hsum.trans (packedRectangle_row_pair_invoice hs choice r)

/-- The selected prefix rectangle slots inherit the physical column invoice. -/
theorem prefixRectangle_column_pair_invoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) :
    (∑ x, (rectanglePairWeight hs choice (fun z => z.2 = c)
      (prefixRectanglePairSlot hrect x)) ^ 2) ≤ 4 := by
  classical
  let w : Fin L × Fin 2 → ℝ := rectanglePairWeight hs choice (fun z => z.2 = c)
  let e := prefixRectanglePairSlot hrect
  have hsub : Finset.univ.image e ⊆ (Finset.univ : Finset (Fin L × Fin 2)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x => (w x) ^ 2) (by intro x hx hx'; exact sq_nonneg (w x))
  rw [Finset.sum_image (by intro x _ y _ h; exact prefixRectanglePairSlot_injective hrect h)] at hsum
  exact hsum.trans (packedRectangle_column_pair_invoice hs choice c)

end
end Sude
