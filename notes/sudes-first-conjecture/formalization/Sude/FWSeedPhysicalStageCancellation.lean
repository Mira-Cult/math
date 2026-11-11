import Sude.FWSeedPhysicalStageTotals
import Sude.ReservedStageSignedCancellation

/-! Signed unused-pool cancellation for supplied actual offset seed stages.
Physical reservation membership, occupancy and stage means remain inputs. -/
namespace Sude
noncomputable section

/-- The actual seed-cell images feed the signed stage/unused-pool identity.
The other reserved cells' signed deviation remains explicit. -/
theorem fw_seed_physical_stages_signed_cancellation {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (a : Cell n ≃ Fin (n * n))
    (mid : Fin 16 → Fin (6 * (n + 8)) → ℝ) (mean : Fin 16 → ℝ)
    (hcells : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (hmid : ∀ j i, mid j i =
      (((entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, i), false)) : ℝ) +
        entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, i), true))) / 2))
    (hmean : ∀ j, (∑ i, mid j i) = (6 * (n + 8) : ℕ) * mean j)
    (reserved : Finset (Cell n)) (stages : Finset (Fin 16)) (r q br : ℕ)
    (hsub : stages.biUnion (physicalPairStageCells
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)) ⊆ reserved)
    (hreservedCard : reserved.card = r * (n + 8) + br)
    (hreserved : reserved.card < n * n) (hline : r + q ≤ n) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j ∈ stages, (mean j - μ)
    let other : ℝ := (∑ z ∈ reserved \ stages.biUnion (physicalPairStageCells cells),
      (entry a z : ℝ)) -
      ((reserved \ stages.biUnion (physicalPairStageCells cells)).card : ℝ) * μ
    let N : ℝ := (n * n - (r * (n + 8) + br) : ℕ)
    let k : ℝ := (n - r - q : ℕ)
    (2 * (6 : ℝ)) * A + k * (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - μ) =
      ((2 * (6 : ℝ)) * A / N) * (((n : ℝ) + 8) * (q : ℝ) - br - 8 * n) - k * other / N := by
  classical
  dsimp only
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  have hd := (physical_pair_stage_cells_disjoint_card cells hcells).1
  have hc := (physical_pair_stage_cells_disjoint_card cells hcells).2
  have hdis : Set.PairwiseDisjoint (↑stages : Set (Fin 16)) (physicalPairStageCells cells) := by
    intro i _ j _ hij
    exact hd (Set.mem_univ i) (Set.mem_univ j) hij
  have hcard : ∀ j ∈ stages, (physicalPairStageCells cells j).card = 2 * 6 * (n + 8) := by
    intro j _
    simpa [cells, ← Nat.mul_assoc] using hc j
  have hsum : ∀ j ∈ stages,
      (∑ z ∈ physicalPairStageCells cells j, (entry a z : ℝ)) =
        (2 * 6 * (n + 8) : ℕ) * mean j := by
    intro j _
    rw [physical_pair_stage_sum_midpoints a cells hcells mid hmid j, hmean j]
    push_cast
    ring
  have result := actual_reserved_stages_signed_cancellation a reserved stages
    (physicalPairStageCells cells) 6 r q br mean hdis hcard hsum hsub hreservedCard hreserved hline
  simpa only [cells, Nat.cast_ofNat] using result

end
end Sude
