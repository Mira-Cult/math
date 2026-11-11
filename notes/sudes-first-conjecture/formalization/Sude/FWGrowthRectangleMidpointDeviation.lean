import Sude.FWGrowthRectangleRowColumnMass
import Sude.FWGrowthNarrowPD2
import Sude.PrefixWeightedPopulationDeviation

/-! Original-stage-centered growth rectangle midpoint contributions on rows
and columns. Complete line sums and ordinary slots remain separate. -/
namespace Sude
noncomputable section

/-- On a supplied trace-indexed square, all growth rectangle pair midpoint
contributions on a row and on a column each differ from their original-stage
mean reference by at most `2*(X/6)`. The bound is global across all stages. -/
theorem fw_growth_rectangle_midpoint_deviation {n L : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X/6) stages)
    (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (a : Cell n ≃ Fin (n*n))
    (hmid : ∀ (j : Fin stages.length) (rect : Fin (4*6)) (pair : Fin 2),
      let i := prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair)
      (((entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice rows cols hr hc ((j,i),true)) : ℝ) +
        entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice rows cols hr hc ((j,i),false))) / 2) =
        growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i))) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let idx := fun z : (Fin stages.length × Fin (4*6)) × Fin 2 =>
      (z.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (z.1.2,z.2))
    let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
      (6*(n+8) : ℕ)
    (∀ r : Fin n,
      |∑ z : (Fin stages.length × Fin (4*6)) × Fin 2,
        physicalPairLineWeight cells (fun c => c.1 = r) (idx z) *
          ((((entry a (cells (idx z,true)) : ℝ) + entry a (cells (idx z,false))) / 2) - μ z.1.1)|
          ≤ 2*(X/6)) ∧
    (∀ c : Fin n,
      |∑ z : (Fin stages.length × Fin (4*6)) × Fin 2,
        physicalPairLineWeight cells (fun q => q.2 = c) (idx z) *
          ((((entry a (cells (idx z,true)) : ℝ) + entry a (cells (idx z,false))) / 2) - μ z.1.1)|
          ≤ 2*(X/6)) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  let idx := fun z : (Fin stages.length × Fin (4*6)) × Fin 2 =>
    (z.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (z.1.2,z.2))
  let pop : Fin stages.length → Finset ℕ := fun j => (stages.get j).lows
  let val : Fin stages.length → ℕ → ℝ := fun j p => growthStageMidpoint (stages.get j) p
  let label := fun z : (Fin stages.length × Fin (4*6)) × Fin 2 =>
    trace.lowAt rfl z.1.1 (ω z.1.1 (idx z).2)
  let deviation := fun z : (Fin stages.length × Fin (4*6)) × Fin 2 =>
    (((entry a (cells (idx z,true)) : ℝ) + entry a (cells (idx z,false))) / 2) -
      (∑ p ∈ pop z.1.1, val z.1.1 p) / (pop z.1.1).card
  have hcard (j : Fin stages.length) : (pop j).card = 6*(n+8) := by
    exact (trace.stage_properties _ (List.get_mem _ _)).2.2.2.1
  have hlabel : ∀ z ∈ (Finset.univ : Finset ((Fin stages.length × Fin (4*6)) × Fin 2)), label z ∈ pop z.1.1 := by
    intro z _
    exact trace.lowAt_mem rfl z.1.1 (ω z.1.1 (idx z).2)
  have hwid : ∀ j, ∀ p ∈ pop j, ∀ q ∈ pop j, val j q - val j p ≤ X/6 := by
    intro j p hp q hq
    exact le_of_lt ((abs_lt.mp (hnarrow (stages.get j) (List.get_mem _ _) q hq p hp)).2)
  have hdev : ∀ z, |deviation z| ≤ X/6 := by
    intro z
    have h := prefix_population_member_mean_width (pop z.1.1) (val z.1.1) (X/6)
      (hwid z.1.1) (label z) (hlabel z (Finset.mem_univ z))
    simpa only [deviation, val, label, hmid, cells, idx] using h
  have hdev_eq (z : (Fin stages.length × Fin (4*6)) × Fin 2) :
      deviation z = (((entry a (cells (idx z,true)) : ℝ) + entry a (cells (idx z,false))) / 2) -
        (∑ p ∈ (stages.get z.1.1).lows, growthStageMidpoint (stages.get z.1.1) p) /
          (6*(n+8) : ℕ) := by
    dsimp only [deviation]
    rw [hcard]
  have hnonneg (line : Cell n → Prop) [DecidablePred line] (z : (Fin stages.length × Fin (4*6)) × Fin 2) :
      0 ≤ physicalPairLineWeight cells line (idx z) := by
    unfold physicalPairLineWeight
    split_ifs <;> norm_num
  have hbound (line : Cell n → Prop) [DecidablePred line]
      (hmass : (∑ z : (Fin stages.length × Fin (4*6)) × Fin 2,
        physicalPairLineWeight cells line (idx z)) ≤ 2) :
      |∑ z : (Fin stages.length × Fin (4*6)) × Fin 2,
        physicalPairLineWeight cells line (idx z) * deviation z| ≤ 2*(X/6) := by
    apply prefix_weighted_centered_bound Finset.univ _ deviation (X/6) (by positivity)
    · intro z _; exact hnonneg line z
    · simpa using hmass
    · intro z _; exact hdev z
  constructor
  · intro r
    have h := hbound (fun c => c.1 = r)
      (fw_growth_rectangle_row_mass offset hoff hs choice rows cols hr hc r)
    simpa only [hdev_eq, cells, idx] using h
  · intro c
    have h := hbound (fun q => q.2 = c)
      (fw_growth_rectangle_column_mass offset hoff hs choice rows cols hr hc c)
    simpa only [hdev_eq, cells, idx] using h

end
end Sude
