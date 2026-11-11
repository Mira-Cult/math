import Sude.FWGrowthOrdinaryDPAllocation
import Sude.PrefixPhysicalSlotGeometry

/-! Exact algebraic partition of growth-pair sums into ordinary and rectangle
slots. This does not provide a line bound or a physical allocation. -/
namespace Sude
noncomputable section

/-- Every stage pair index appears exactly once in either the ordinary
network slots or the rectangle pair slots. -/
theorem fw_growth_stage_pair_sum_split (n : ℕ) (f : Fin (6*(n+8)) → ℝ) :
    (∑ i, f i) = (∑ i ∈ fwGrowthOrdinarySlots n, f i) +
      ∑ x : Fin (4*6) × Fin 2,
        f (prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) x) := by
  classical
  let hfit : (4*6)*2 + 2*(3*n) ≤ 6*(n+8) := by omega
  let hdiag : (4*6)*2 ≤ 6*(n+8) := by omega
  let hexact : (4*6)*2 + 2*(3*n) = 6*(n+8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  have hsum : (∑ i, f i) =
      (∑ x : Fin (4*6) × Fin 2, f (prefixDiagonalPairIndex hdiag x)) +
      ∑ x : Fin 2 × Fin 3 × Fin n, f (prefixOrdinaryPairIndex hfit x) := by
    calc
      _ = ∑ t : PrefixStagePair 6 3 n, f (e t) := (e.sum_comp f).symm
      _ = _ := by simp [e, prefixStagePairSlot, Fintype.sum_sum_type]
  have hord : (∑ i ∈ fwGrowthOrdinarySlots n, f i) =
      ∑ x : Fin 2 × Fin 3 × Fin n, f (prefixOrdinaryPairIndex hfit x) := by
    unfold fwGrowthOrdinarySlots
    rw [Finset.sum_image (prefixOrdinaryPairIndex_injective hfit).injOn]
  rw [hord]
  linarith

/-- Across all stage occurrences, the ordinary population and the indexed
rectangle pairs partition an arbitrary growth-pair sum. -/
theorem fw_growth_pair_sum_split {n P : ℕ} (f : Fin P × Fin (6*(n+8)) → ℝ) :
    (∑ s : Fin P × Fin (6*(n+8)), f s) =
      (∑ s : {s // s ∈ fwGrowthOrdinaryPopulation n P}, f s.val) +
      ∑ x : (Fin P × Fin (4*6)) × Fin 2,
        f (x.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (x.1.2,x.2)) := by
  classical
  have hord : (∑ s : {s // s ∈ fwGrowthOrdinaryPopulation n P}, f s.val) =
      ∑ j : Fin P, ∑ i ∈ fwGrowthOrdinarySlots n, f (j,i) := by
    rw [Finset.sum_coe_sort]
    simp [fwGrowthOrdinaryPopulation, Finset.sum_product]
  have hrect : (∑ x : (Fin P × Fin (4*6)) × Fin 2,
      f (x.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (x.1.2,x.2))) =
      ∑ j : Fin P, ∑ x : Fin (4*6) × Fin 2,
        f (j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) x) := by
    simp [Fintype.sum_prod_type]
  rw [hord, hrect, Fintype.sum_prod_type]
  simp_rw [fw_growth_stage_pair_sum_split n]
  rw [Finset.sum_add_distrib]

/-- Centered midpoint discrepancy decomposes with the same original stage
reference into the two nonoverlapping slot families. -/
theorem fw_growth_centered_midpoint_split {n P : ℕ}
    (w midpoint : Fin P × Fin (6*(n+8)) → ℝ) (μ : Fin P → ℝ) :
    (∑ s : Fin P × Fin (6*(n+8)), w s * (midpoint s - μ s.1)) =
      (∑ s : {s // s ∈ fwGrowthOrdinaryPopulation n P},
        w s.val * (midpoint s.val - μ s.val.1)) +
      ∑ x : (Fin P × Fin (4*6)) × Fin 2,
        w (x.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (x.1.2,x.2)) *
        (midpoint (x.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (x.1.2,x.2)) - μ x.1.1) := by
  exact fw_growth_pair_sum_split (fun s => w s * (midpoint s - μ s.1))

end
end Sude
