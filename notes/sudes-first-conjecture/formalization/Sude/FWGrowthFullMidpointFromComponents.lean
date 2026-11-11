import Sude.FWGrowthPairSumDecomposition
import Sude.FWGrowthRectangleMidpointDeviation

/-! Combine same-square ordinary midpoint estimates with the actual growth
rectangle midpoint estimate, without asserting full entry-line bounds. -/
namespace Sude
noncomputable section

/-- If the ordinary midpoint contribution is bounded about the original
stage means on every row and column, the full growth midpoint contribution
on the same square costs at most an additional `2*(X/6)` for rectangle slots.
The ordinary bound is supplied; pair-gap orientations and other families
remain separate. -/
theorem fw_growth_full_midpoint_from_components {n L : ℕ} {initial final : Finset ℕ}
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
        growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i)))
    (B : ℝ)
    (hordR : ∀ r : Fin n,
      let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc
      let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6*(n+8) : ℕ)
      |∑ s : {s // s ∈ fwGrowthOrdinaryPopulation n stages.length},
        physicalPairLineWeight cells (fun c => c.1 = r) s.val *
          ((((entry a (cells (s.val,true)) : ℝ) + entry a (cells (s.val,false))) / 2) - μ s.val.1)| ≤ B)
    (hordC : ∀ c : Fin n,
      let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc
      let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6*(n+8) : ℕ)
      |∑ s : {s // s ∈ fwGrowthOrdinaryPopulation n stages.length},
        physicalPairLineWeight cells (fun q => q.2 = c) s.val *
          ((((entry a (cells (s.val,true)) : ℝ) + entry a (cells (s.val,false))) / 2) - μ s.val.1)| ≤ B) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
      (6*(n+8) : ℕ)
    (∀ r : Fin n,
      |∑ s : Fin stages.length × Fin (6*(n+8)),
        physicalPairLineWeight cells (fun c => c.1 = r) s *
          ((((entry a (cells (s,true)) : ℝ) + entry a (cells (s,false))) / 2) - μ s.1)| ≤ B + 2*(X/6)) ∧
    (∀ c : Fin n,
      |∑ s : Fin stages.length × Fin (6*(n+8)),
        physicalPairLineWeight cells (fun q => q.2 = c) s *
          ((((entry a (cells (s,true)) : ℝ) + entry a (cells (s,false))) / 2) - μ s.1)| ≤ B + 2*(X/6)) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  let μ : Fin stages.length → ℝ := fun j =>
    (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / (6*(n+8) : ℕ)
  let mid : Fin stages.length × Fin (6*(n+8)) → ℝ := fun s =>
    (((entry a (cells (s,true)) : ℝ) + entry a (cells (s,false))) / 2)
  have hrect := fw_growth_rectangle_midpoint_deviation trace X hX hnarrow ω
    offset hoff hs choice rows cols hr hc a hmid
  constructor
  · intro r
    have heq := fw_growth_centered_midpoint_split
      (fun s => physicalPairLineWeight cells (fun c => c.1 = r) s) mid μ
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (hordR r) (hrect.1 r))
  · intro c
    have heq := fw_growth_centered_midpoint_split
      (fun s => physicalPairLineWeight cells (fun q => q.2 = c) s) mid μ
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (hordC c) (hrect.2 c))

end
end Sude
