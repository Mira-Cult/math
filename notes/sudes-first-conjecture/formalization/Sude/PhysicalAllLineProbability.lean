import Sude.DiagonalSlotBounds
import Sude.PhysicalRowColumnProbability

/-! Simultaneous physical midpoint-slot control for all labelled lines. -/
namespace Sude
noncomputable section

/-- The labelled rows, columns, main diagonal, and antidiagonal share the
same injectively occupied physical pair slots. -/
def physicalAllLineSlots {P d layers n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) :
    Fin ((n + n) + 2) → Fin P → Finset (Fin Q) := fun _ _ => physicalPrefixSlots hfit hdiag

/-- Actual physical pair-incidence weights for all labelled required lines. -/
noncomputable def physicalAllLineWeights {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (l : Fin ((n + n) + 2)) (j : Fin P) (q : Fin Q) : ℝ :=
  let choice := bridgeDiagonalChoice hrect otherChoice
  match (finSumFinEquiv (m := n + n) (n := 2)).symm l with
  | Sum.inl rc => physicalRowColumnWeights hfit hdiag hrect hs choice rows cols hrows hcols rc j q
  | Sum.inr diag =>
      if diag = 0 then physicalDiagonalSlotWeight hfit hdiag hrect hs choice (fun c => c ∈ mainCells n) j q
      else physicalDiagonalSlotWeight hfit hdiag hrect hs choice (fun c => c ∈ antiCells n) j q

/-- One permutation of each actual physical stage controls all `2n+2`
labelled midpoint-slot forms using the proved physical incidence invoice.
The identities with completed square-line errors and controller arithmetic
remain separate obligations. -/
theorem physical_all_line_midpoint_allocation {P d layers n L Q : ℕ}
    (hQ : 0 < Q) (hd : d = 2 * layers)
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (otherChoice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (values : Fin P → Fin Q → ℝ) (lo upper : Fin P → ℝ) (z : ℝ)
    (hvalues : ∀ j a, values j a ∈ Set.Icc (lo j) (upper j))
    (hwidth : ∀ j, (upper j - lo j) ^ 2 ≤ z ^ 2) :
    ∃ ω : Fin P → Equiv.Perm (Fin Q), ∀ l,
      |stageLineCentered (physicalAllLineSlots hfit hdiag)
        (physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols) values l ω| ≤
      Real.sqrt (((3 * (d : ℝ) * (∑ j, (upper j - lo j) ^ 2) + 4 * z ^ 2) *
        Real.log (4 * (((n + n) + 2 : ℕ) : ℝ))) / 2) := by
  let V : ℝ := 3 * (d : ℝ) * (∑ j, (upper j - lo j) ^ 2) + 4 * z ^ 2
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hlu : ∀ j, lo j ≤ upper j := by
    intro j
    exact (hvalues j ⟨0, hQ⟩).1.trans (hvalues j ⟨0, hQ⟩).2
  have hnonneg : ∀ l j q, q ∈ physicalAllLineSlots hfit hdiag l j →
      0 ≤ physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols l j q := by
    intro l j q _
    cases hl : (finSumFinEquiv (m := n + n) (n := 2)).symm l with
    | inl rc =>
      cases hrc : (finSumFinEquiv (m := n) (n := n)).symm rc with
      | inl r =>
        simpa [physicalAllLineWeights, physicalRowColumnWeights, hl, hrc] using
          physicalRowSlotWeight_nonneg hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
            rows cols hrows hcols j r q
      | inr c =>
        simpa [physicalAllLineWeights, physicalRowColumnWeights, hl, hrc] using
          physicalColumnSlotWeight_nonneg hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
            rows cols hrows hcols j c q
    | inr diag =>
      by_cases hzero : diag = 0
      · simpa [physicalAllLineWeights, hl, hzero] using
          physicalDiagonalSlotWeight_nonneg hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
            (fun c => c ∈ mainCells n) j q
      · simpa [physicalAllLineWeights, hl, hzero] using
          physicalDiagonalSlotWeight_nonneg hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
            (fun c => c ∈ antiCells n) j q
  have hinvoice : ∀ l, (∑ j, (upper j - lo j) ^ 2 *
      ∑ q ∈ physicalAllLineSlots hfit hdiag l j,
        (physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols l j q) ^ 2) ≤ V := by
    intro l
    cases hl : (finSumFinEquiv (m := n + n) (n := 2)).symm l with
    | inl rc =>
      cases hrc : (finSumFinEquiv (m := n) (n := n)).symm rc with
      | inl r =>
        simpa [physicalAllLineSlots, physicalAllLineWeights, physicalRowColumnWeights, hl, hrc, V] using
          physicalRowSlot_weighted_invoice hd hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
            rows cols hrows hcols reservedRows packedRows r (fun j => upper j - lo j) z hwidth
      | inr c =>
        simpa [physicalAllLineSlots, physicalAllLineWeights, physicalRowColumnWeights, hl, hrc, V] using
          physicalColumnSlot_weighted_invoice hd hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
            rows cols hrows hcols reservedCols packedCols c (fun j => upper j - lo j) z hwidth
    | inr diag =>
      by_cases hzero : diag = 0
      · simpa [physicalAllLineSlots, physicalAllLineWeights, hl, hzero, V] using
          physicalMainSlot_weighted_invoice hfit hdiag hrect hs hL otherChoice (fun j => upper j - lo j) z
      · simpa [physicalAllLineSlots, physicalAllLineWeights, hl, hzero, V] using
          physicalAntiSlot_weighted_invoice hfit hdiag hrect hs hL otherChoice (fun j => upper j - lo j) z
  exact stageLines_exists_of_squared_invoice (by omega) _ _ values lo upper V hV hlu hnonneg hvalues hinvoice

end
end Sude
