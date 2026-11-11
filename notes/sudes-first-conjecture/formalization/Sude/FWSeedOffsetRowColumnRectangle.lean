import Sude.FWSeedRectangleOffset
import Sude.PrefixRectangleInvoice
import Sude.FWSeedOffsetDiagonalInvoice
import Sude.StageInvoiceComposition

/-! Row and column incidence for the actual offset seed rectangles. -/
namespace Sude
noncomputable section

/-- Map each stage/rectangle/pair label to its actual offset seed rectangle. -/
def fwSeedOffsetPairSlot {L : ℕ} (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) :
    ((Fin 16 × Fin (4 * 6)) × Fin 2) → Fin L × Fin 2 :=
  fun x => (fwSeedRectangle hseed (finProdFinEquiv x.1), x.2)

theorem fwSeedOffsetPairSlot_injective {L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) :
    Function.Injective (fwSeedOffsetPairSlot hseed) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have hi : i = j := finProdFinEquiv.injective
    (fwSeedRectangle_injective hseed (congrArg Prod.fst h))
  have hp : p = q := congrArg Prod.snd h
  exact Prod.ext hi hp

/-- All actual offset seed rectangle pairs have row squared-incidence invoice ≤ 4. -/
theorem fw_seed_offset_row_pair_invoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    (∑ x, (rectanglePairWeight hs choice (fun c => c.1 = r)
      (fwSeedOffsetPairSlot hseed x)) ^ 2) ≤ 4 := by
  classical
  let w : Fin L × Fin 2 → ℝ := rectanglePairWeight hs choice (fun c => c.1 = r)
  let e := fwSeedOffsetPairSlot hseed
  have hsub : Finset.univ.image e ⊆ (Finset.univ : Finset (Fin L × Fin 2)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x => (w x) ^ 2) (by intro x hx hx'; exact sq_nonneg (w x))
  rw [Finset.sum_image (by intro x _ y _ h; exact fwSeedOffsetPairSlot_injective hseed h)] at hsum
  exact hsum.trans (packedRectangle_row_pair_invoice hs choice r)

/-- All actual offset seed rectangle pairs have column squared-incidence invoice ≤ 4. -/
theorem fw_seed_offset_column_pair_invoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) :
    (∑ x, (rectanglePairWeight hs choice (fun z => z.2 = c)
      (fwSeedOffsetPairSlot hseed x)) ^ 2) ≤ 4 := by
  classical
  let w : Fin L × Fin 2 → ℝ := rectanglePairWeight hs choice (fun z => z.2 = c)
  let e := fwSeedOffsetPairSlot hseed
  have hsub : Finset.univ.image e ⊆ (Finset.univ : Finset (Fin L × Fin 2)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x => (w x) ^ 2) (by intro x hx hx'; exact sq_nonneg (w x))
  rw [Finset.sum_image (by intro x _ y _ h; exact fwSeedOffsetPairSlot_injective hseed h)] at hsum
  exact hsum.trans (packedRectangle_column_pair_invoice hs choice c)

/-- Grouping by stage preserves the bound for a physical row. -/
theorem fw_seed_offset_row_rectangle_stage_invoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    (∑ j, fwSeedOffsetRectangleStageInvoice hseed hs choice (fun c => c.1 = r) j) ≤ 4 := by
  have h := fw_seed_offset_row_pair_invoice hseed hs choice r
  simpa [fwSeedOffsetRectangleStageInvoice, fwSeedOffsetPairSlot, Fintype.sum_prod_type] using h

/-- Grouping by stage preserves the bound for a physical column. -/
theorem fw_seed_offset_column_rectangle_stage_invoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) :
    (∑ j, fwSeedOffsetRectangleStageInvoice hseed hs choice (fun x => x.2 = c) j) ≤ 4 := by
  have h := fw_seed_offset_column_pair_invoice hseed hs choice c
  simpa [fwSeedOffsetRectangleStageInvoice, fwSeedOffsetPairSlot, Fintype.sum_prod_type] using h

theorem fw_seed_offset_rectangle_stage_invoice_nonneg {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin 16) :
    0 ≤ fwSeedOffsetRectangleStageInvoice hseed hs choice line j := by
  apply Finset.sum_nonneg
  intro rect _
  apply Finset.sum_nonneg
  intro pair _
  exact sq_nonneg _

/-- Add any supplied ordinary-stage invoice to the actual offset rectangle
invoice, keeping the source's width and ordinary bounds explicit. -/
theorem fw_seed_offset_row_combined_width_invoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) (width ordinary : Fin 16 → ℝ) (z : ℝ)
    (hord : ∀ j, ordinary j ≤ 18) (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * (ordinary j +
      fwSeedOffsetRectangleStageInvoice hseed hs choice (fun c => c.1 = r) j)) ≤
      18 * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  have h := stage_squared_invoice_of_ordinary_and_rectangles width ordinary
    (fwSeedOffsetRectangleStageInvoice hseed hs choice (fun c => c.1 = r)) 6 z
    (by intro j; norm_num; exact hord j)
    (fw_seed_offset_rectangle_stage_invoice_nonneg hseed hs choice _)
    (fw_seed_offset_row_rectangle_stage_invoice hseed hs choice r) hwidth
  norm_num at h ⊢
  exact h

/-- The same bound for a physical column. -/
theorem fw_seed_offset_column_combined_width_invoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) (width ordinary : Fin 16 → ℝ) (z : ℝ)
    (hord : ∀ j, ordinary j ≤ 18) (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * (ordinary j +
      fwSeedOffsetRectangleStageInvoice hseed hs choice (fun x => x.2 = c) j)) ≤
      18 * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  have h := stage_squared_invoice_of_ordinary_and_rectangles width ordinary
    (fwSeedOffsetRectangleStageInvoice hseed hs choice (fun x => x.2 = c)) 6 z
    (by intro j; norm_num; exact hord j)
    (fw_seed_offset_rectangle_stage_invoice_nonneg hseed hs choice _)
    (fw_seed_offset_column_rectangle_stage_invoice hseed hs choice c) hwidth
  norm_num at h ⊢
  exact h

end
end Sude
