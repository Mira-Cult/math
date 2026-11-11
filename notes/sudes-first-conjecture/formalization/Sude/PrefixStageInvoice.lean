import Sude.PrefixRectangleInvoice
import Sude.StageInvoiceComposition

/-! Group the actual selected prefix rectangle incidences by stage. -/
namespace Sude
noncomputable section

/-- The squared physical rectangle-pair weights for one selected stage. -/
noncomputable def prefixRectangleStageInvoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin P) : ℝ :=
  ∑ rect : Fin (4 * d), ∑ pair : Fin 2,
    (rectanglePairWeight hs choice line (prefixRectanglePairSlot hrect ((j, rect), pair))) ^ 2

/-- All stagewise rectangle invoices total at most four for a physical row. -/
theorem prefixRectangle_row_stage_invoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    (∑ j, prefixRectangleStageInvoice hrect hs choice (fun c => c.1 = r) j) ≤ 4 := by
  have h := prefixRectangle_row_pair_invoice hrect hs choice r
  simpa [prefixRectangleStageInvoice, Fintype.sum_prod_type] using h

/-- All stagewise rectangle invoices total at most four for a physical column. -/
theorem prefixRectangle_column_stage_invoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) :
    (∑ j, prefixRectangleStageInvoice hrect hs choice (fun x => x.2 = c) j) ≤ 4 := by
  have h := prefixRectangle_column_pair_invoice hrect hs choice c
  simpa [prefixRectangleStageInvoice, Fintype.sum_prod_type] using h

/-- The selected rectangle invoice is a sum of nonnegative squares. -/
theorem prefixRectangleStageInvoice_nonneg {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin P) :
    0 ≤ prefixRectangleStageInvoice hrect hs choice line j := by
  apply Finset.sum_nonneg
  intro rect _
  apply Finset.sum_nonneg
  intro pair _
  exact sq_nonneg _

/-- With the ordinary stage invoice supplied, the actual rectangle geometry
provides the remaining row term of the width-weighted invoice. -/
theorem prefix_row_combined_width_invoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) (width ordinary : Fin P → ℝ) (z : ℝ)
    (hord : ∀ j, ordinary j ≤ 3 * (d : ℝ))
    (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * (ordinary j +
      prefixRectangleStageInvoice hrect hs choice (fun c => c.1 = r) j)) ≤
      3 * (d : ℝ) * (∑ j, (width j) ^ 2) + 4 * z ^ 2 :=
  stage_squared_invoice_of_ordinary_and_rectangles width ordinary
    (prefixRectangleStageInvoice hrect hs choice (fun c => c.1 = r)) d z hord
    (prefixRectangleStageInvoice_nonneg hrect hs choice _)
    (prefixRectangle_row_stage_invoice hrect hs choice r) hwidth

/-- The corresponding width-weighted bound for a physical column. -/
theorem prefix_column_combined_width_invoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) (width ordinary : Fin P → ℝ) (z : ℝ)
    (hord : ∀ j, ordinary j ≤ 3 * (d : ℝ))
    (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * (ordinary j +
      prefixRectangleStageInvoice hrect hs choice (fun x => x.2 = c) j)) ≤
      3 * (d : ℝ) * (∑ j, (width j) ^ 2) + 4 * z ^ 2 :=
  stage_squared_invoice_of_ordinary_and_rectangles width ordinary
    (prefixRectangleStageInvoice hrect hs choice (fun x => x.2 = c)) d z hord
    (prefixRectangleStageInvoice_nonneg hrect hs choice _)
    (prefixRectangle_column_stage_invoice hrect hs choice c) hwidth

end
end Sude
