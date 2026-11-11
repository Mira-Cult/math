import Sude.FWSeedExistingReallocation
import Sude.ReservedStageFamilyTotal
import Mathlib.Data.Fintype.BigOperators

/-! Physical seed-stage totals from an injective existing pair-cell map.
The physical placement, injection, and midpoint data are supplied. -/
namespace Sude
noncomputable section

/-- The physical endpoints of one stage of a pair-cell family. -/
def physicalPairStageCells {n P Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (j : Fin P) : Finset (Cell n) :=
  Finset.univ.image (fun x : Fin Q × Bool => cells ((j, x.1), x.2))

/-- Injective pair cells give disjoint stage images of exactly `2*Q` cells. -/
theorem physical_pair_stage_cells_disjoint_card {n P Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin P)) (physicalPairStageCells cells) ∧
      ∀ j, (physicalPairStageCells cells j).card = 2 * Q := by
  classical
  constructor
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro c hi hj
    obtain ⟨⟨x, s⟩, _, hx⟩ := Finset.mem_image.mp hi
    obtain ⟨⟨y, t⟩, _, hy⟩ := Finset.mem_image.mp hj
    have h := hcells (hx.trans hy.symm)
    exact hij (congrArg (fun z => z.1.1) h)
  · intro j
    unfold physicalPairStageCells
    rw [Finset.card_image_iff.mpr]
    · simp [Fintype.card_prod, Nat.mul_comm]
    · intro x _ y _ h
      have hh := hcells h
      exact Prod.ext (congrArg (fun z => z.1.2) hh)
        (congrArg (fun z : (Fin P × Fin Q) × Bool => z.2) hh)

/-- The sum over a stage is twice the sum of its supplied pair midpoints. -/
theorem physical_pair_stage_sum_midpoints {n P Q : ℕ}
    (a : Cell n ≃ Fin (n * n)) (cells : (Fin P × Fin Q) × Bool → Cell n)
    (hcells : Function.Injective cells) (mid : Fin P → Fin Q → ℝ)
    (hmid : ∀ j i, mid j i =
      (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2))
    (j : Fin P) :
    (∑ c ∈ physicalPairStageCells cells j, (entry a c : ℝ)) = 2 * ∑ i, mid j i := by
  classical
  unfold physicalPairStageCells
  rw [Finset.sum_image]
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_bool, hmid]
    ring
  · intro x _ y _ h
    have hh := hcells h
    exact Prod.ext (congrArg (fun z => z.1.2) hh)
      (congrArg (fun z : (Fin P × Fin Q) × Bool => z.2) hh)

/-- Actual offset seed stages satisfy the uniform physical-stage interface
when their supplied midpoint sums have the stated stage means. -/
theorem fw_seed_physical_stage_totals {n L : ℕ}
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
    (stages : Finset (Fin 16)) :
    let stageCells := physicalPairStageCells (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
    (stages.biUnion stageCells).card = stages.card * (2 * 6 * (n + 8)) ∧
    (∑ c ∈ stages.biUnion stageCells, (entry a c : ℝ)) -
        ((stages.biUnion stageCells).card : ℝ) *
          centralEntriesMean (prescribedPoolValues n) centralPoolValue =
      2 * (6 : ℝ) * ((n : ℝ) + 8) *
        ∑ j ∈ stages, (mean j - centralEntriesMean (prescribedPoolValues n) centralPoolValue) := by
  classical
  dsimp only
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  have hd := (physical_pair_stage_cells_disjoint_card cells hcells).1
  have hc := (physical_pair_stage_cells_disjoint_card cells hcells).2
  apply reserved_uniform_stage_family_signed_total a stages (physicalPairStageCells cells) 6 mean
  · intro i _ j _ hij
    exact hd (Set.mem_univ i) (Set.mem_univ j) hij
  · intro j _
    simpa [cells, ← Nat.mul_assoc] using hc j
  · intro j _
    rw [physical_pair_stage_sum_midpoints a cells hcells mid hmid j, hmean j]
    push_cast
    ring

end
end Sude
