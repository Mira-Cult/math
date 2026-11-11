import Sude.FWGrowthStageOrientationZero
import Sude.StageGapPhysicalLineTransfer

/-! Actual growth-image row/column entry bounds on the supplied ordered square.
The line residual is retained and may contain every nongrowth contribution.
Later within-pair switches leave cell orientations unchanged but may invalidate
the signed common-gap premise used in the cancellation. -/
namespace Sude
noncomputable section

/-- On one supplied square with injective actual growth cells and a common
physical gap within each stage, the row/column midpoint bounds transfer to
physical entries. The stage-mean reference uses actual pair incidences and
the entire nongrowth line complement remains explicit. -/
theorem fw_growth_physical_row_column_bound {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (a : Cell n ≃ Fin (n*n)) (μ : Fin P → ℝ) (gap : Fin P → ℕ) (B : ℝ)
    (hcells : Function.Injective (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc))
    (hgap : ∀ j i, entry a ((btGrowingOffsetPairCells (Q := 6*(n+8))
        (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) ((j,i),true)) =
      entry a ((btGrowingOffsetPairCells (Q := 6*(n+8))
        (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) ((j,i),false)) + gap j)
    (hrow : ∀ r : Fin n,
      |∑ p : Fin P × Fin (6*(n+8)), physicalPairLineWeight
        (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc)
        (fun c => c.1 = r) p *
        ((((entry a ((btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) (p,false)) : ℝ) +
          entry a ((btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) (p,true))) / 2) - μ p.1)| ≤ B)
    (hcol : ∀ c : Fin n,
      |∑ p : Fin P × Fin (6*(n+8)), physicalPairLineWeight
        (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc)
        (fun z => z.2 = c) p *
        ((((entry a ((btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) (p,false)) : ℝ) +
          entry a ((btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) (p,true))) / 2) - μ p.1)| ≤ B) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∀ r : Fin n, |(∑ c ∈ rowCells r, (entry a c : ℝ)) -
      (∑ c ∈ rowCells r \ Finset.univ.image cells, (entry a c : ℝ)) -
      (∑ p : Fin P × Fin (6*(n+8)), physicalPairLineWeight cells (fun c => c.1 = r) p * μ p.1)| ≤ B) ∧
    (∀ c : Fin n, |(∑ z ∈ columnCells c, (entry a z : ℝ)) -
      (∑ z ∈ columnCells c \ Finset.univ.image cells, (entry a z : ℝ)) -
      (∑ p : Fin P × Fin (6*(n+8)), physicalPairLineWeight cells (fun z => z.2 = c) p * μ p.1)| ≤ B) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  constructor
  · intro r
    have hz : ∀ j, ∑ i : Fin (6*(n+8)), physicalPairLineOrientation cells (fun c => c ∈ rowCells r) (j,i) = 0 := by
      intro j
      simpa only [mem_rowCells] using fw_growth_stage_row_orientation_zero offset hoff hs choice rows cols hr hc j r
    have hh := stage_gap_physical_line_zero_orientation_bound cells hcells (rowCells r) a μ gap B hgap hz (by simpa only [mem_rowCells] using hrow r)
    simpa only [mem_rowCells] using hh
  · intro c
    have hz : ∀ j, ∑ i : Fin (6*(n+8)), physicalPairLineOrientation cells (fun z => z ∈ columnCells c) (j,i) = 0 := by
      intro j
      simpa only [mem_columnCells] using fw_growth_stage_column_orientation_zero offset hoff hs choice rows cols hr hc j c
    have hh := stage_gap_physical_line_zero_orientation_bound cells hcells (columnCells c) a μ gap B hgap hz (by simpa only [mem_columnCells] using hcol c)
    simpa only [mem_columnCells] using hh

end
end Sude
