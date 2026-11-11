import Sude.PhysicalSlotNonnegative
import Sude.StageSquaredInvoice

/-! Simultaneous midpoint-slot bounds for all physical rows and columns. -/
namespace Sude
noncomputable section

/-- Row and column labels use the same distinct physical pair slots. -/
def physicalRowColumnSlots {P d layers n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) :
    Fin (n + n) → Fin P → Finset (Fin Q) := fun _ _ => physicalPrefixSlots hfit hdiag

/-- Each labelled row or column receives its actual physical incidence weights. -/
noncomputable def physicalRowColumnWeights {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (l : Fin (n + n)) (j : Fin P) (q : Fin Q) : ℝ :=
  match (finSumFinEquiv (m := n) (n := n)).symm l with
  | Sum.inl r => physicalRowSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j r q
  | Sum.inr c => physicalColumnSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j c q

/-- One set of stage permutations controls all row and column midpoint-slot
forms, using the actual physical incidence invoice. The diagonals and the
identification with completed square-line errors are separate obligations. -/
theorem physical_row_column_midpoint_allocation {P d layers n L Q : ℕ}
    (hn : 0 < n) (hQ : 0 < Q) (hd : d = 2 * layers)
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (values : Fin P → Fin Q → ℝ) (lo upper : Fin P → ℝ) (z : ℝ)
    (hvalues : ∀ j a, values j a ∈ Set.Icc (lo j) (upper j))
    (hwidth : ∀ j, (upper j - lo j) ^ 2 ≤ z ^ 2) :
    ∃ ω : Fin P → Equiv.Perm (Fin Q), ∀ l,
      |stageLineCentered (physicalRowColumnSlots hfit hdiag)
        (physicalRowColumnWeights hfit hdiag hrect hs choice rows cols hrows hcols) values l ω| ≤
      Real.sqrt (((3 * (d : ℝ) * (∑ j, (upper j - lo j) ^ 2) + 4 * z ^ 2) *
        Real.log (4 * ((n + n : ℕ) : ℝ))) / 2) := by
  let V : ℝ := 3 * (d : ℝ) * (∑ j, (upper j - lo j) ^ 2) + 4 * z ^ 2
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hlu : ∀ j, lo j ≤ upper j := by
    intro j
    exact (hvalues j ⟨0, hQ⟩).1.trans (hvalues j ⟨0, hQ⟩).2
  have hnonneg : ∀ l j q, q ∈ physicalRowColumnSlots hfit hdiag l j →
      0 ≤ physicalRowColumnWeights hfit hdiag hrect hs choice rows cols hrows hcols l j q := by
    intro l j q _
    cases hl : (finSumFinEquiv (m := n) (n := n)).symm l with
    | inl r =>
      simpa [physicalRowColumnWeights, hl] using
        physicalRowSlotWeight_nonneg hfit hdiag hrect hs choice rows cols hrows hcols j r q
    | inr c =>
      simpa [physicalRowColumnWeights, hl] using
        physicalColumnSlotWeight_nonneg hfit hdiag hrect hs choice rows cols hrows hcols j c q
  have hinvoice : ∀ l, (∑ j, (upper j - lo j) ^ 2 *
      ∑ q ∈ physicalRowColumnSlots hfit hdiag l j,
        (physicalRowColumnWeights hfit hdiag hrect hs choice rows cols hrows hcols l j q) ^ 2) ≤ V := by
    intro l
    cases hl : (finSumFinEquiv (m := n) (n := n)).symm l with
    | inl r =>
      simpa [physicalRowColumnSlots, physicalRowColumnWeights, hl, V] using
        physicalRowSlot_weighted_invoice hd hfit hdiag hrect hs choice rows cols hrows hcols
          reservedRows packedRows r (fun j => upper j - lo j) z hwidth
    | inr c =>
      simpa [physicalRowColumnSlots, physicalRowColumnWeights, hl, V] using
        physicalColumnSlot_weighted_invoice hd hfit hdiag hrect hs choice rows cols hrows hcols
          reservedCols packedCols c (fun j => upper j - lo j) z hwidth
  exact stageLines_exists_of_squared_invoice (by omega) _ _ values lo upper V hV hlu hnonneg hvalues hinvoice

end
end Sude
