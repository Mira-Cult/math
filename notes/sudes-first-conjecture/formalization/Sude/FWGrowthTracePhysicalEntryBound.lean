import Sude.FWGrowthPhysicalRowColumnBound
import Sude.FWGrowthPermutedTraceMidpoints

/-! Transfer supplied growth midpoint bounds to physical row/column entries
on the same ordered trace-placed square. All other line entries remain explicit. -/
namespace Sude
noncomputable section

/-- The final trace placement supplies its own cell injectivity and
stage-specific signed gaps, so a bound on that square's centered growth
midpoints transfers to physical entries without adding a new placement
hypothesis. This uses no later switched or centered square. -/
theorem fw_growth_trace_midpoint_to_physical_lines {n L : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (a : Cell n ≃ Fin (n*n)) (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (hplaced : ∀ x, entry a ((btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) x) =
      (trace.poolValues rfl hpool (stagePairPermutation ω x)).val)
    (μ : Fin stages.length → ℝ) (B : ℝ)
    (hrow : ∀ r : Fin n,
      |∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight
        (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc)
        (fun c => c.1 = r) p *
        ((((entry a ((btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) (p,true)) : ℝ) +
          entry a ((btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) (p,false))) / 2) - μ p.1)| ≤ B)
    (hcol : ∀ c : Fin n,
      |∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight
        (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc)
        (fun z => z.2 = c) p *
        ((((entry a ((btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) (p,true)) : ℝ) +
          entry a ((btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc) (p,false))) / 2) - μ p.1)| ≤ B) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∀ r : Fin n, |(∑ c ∈ rowCells r, (entry a c : ℝ)) -
      (∑ c ∈ rowCells r \ Finset.univ.image cells, (entry a c : ℝ)) -
      (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight cells (fun c => c.1 = r) p * μ p.1)| ≤ B) ∧
    (∀ c : Fin n, |(∑ z ∈ columnCells c, (entry a z : ℝ)) -
      (∑ z ∈ columnCells c \ Finset.univ.image cells, (entry a z : ℝ)) -
      (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight cells (fun z => z.2 = c) p * μ p.1)| ≤ B) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  obtain ⟨hinj, hgap, _⟩ := growth_permuted_trace_midpoints trace rfl hpool cells a ω hplaced
  apply fw_growth_physical_row_column_bound offset hoff hs choice rows cols hr hc a μ
    (fun j => (BTStageTrace.stageAt stages rfl j).gap) B hinj hgap
  · intro r
    have heq : (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight cells
        (fun c => c.1 = r) p *
        ((((entry a (cells (p,false)) : ℝ) + entry a (cells (p,true))) / 2) - μ p.1)) =
      ∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight cells
        (fun c => c.1 = r) p *
        ((((entry a (cells (p,true)) : ℝ) + entry a (cells (p,false))) / 2) - μ p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [add_comm (entry a (cells (p,false)) : ℝ)]
    rw [heq]
    exact hrow r
  · intro c
    have heq : (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight cells
        (fun z => z.2 = c) p *
        ((((entry a (cells (p,false)) : ℝ) + entry a (cells (p,true))) / 2) - μ p.1)) =
      ∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight cells
        (fun z => z.2 = c) p *
        ((((entry a (cells (p,true)) : ℝ) + entry a (cells (p,false))) / 2) - μ p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [add_comm (entry a (cells (p,false)) : ℝ)]
    rw [heq]
    exact hcol c

end
end Sude
