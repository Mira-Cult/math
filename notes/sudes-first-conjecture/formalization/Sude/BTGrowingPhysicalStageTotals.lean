import Sude.PrefixPhysicalLineSum
import Sude.BTGrowingOffsetPhysical
import Sude.BTGrowingPoolValues
import Sude.FWSeedPhysicalStageTotals

/-! Physical stage totals for an explicitly supplied growing-trace placement.
No theta witness, mean estimate, or full-line bound is asserted. -/
namespace Sude
noncomputable section

/-- Reindex the actual offset-growth roles by stage, pair and endpoint. -/
def btGrowingOffsetPairCells {P d r n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (offset : ℕ) (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P * r) (hc : cols.length = P * r) :
    (Fin P × Fin Q) × Bool → Cell n :=
  fun x => btGrowingOffsetCells offset hoff hs choice rows cols hr hc
    ((prefixPhysicalInputEquiv hfit hdiag hexact).symm x)

/-- Exact physical injection, stage disjointness, stage sizes, and same-square
midpoint sums for the supplied trace placement. Stage-cell unions remain in
the actual growth-role image. Empty stage or pair index types are allowed. -/
theorem bt_growing_physical_stage_totals
    {g Q n P d r L : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (offset : ℕ) (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P * r) (hc : cols.length = P * r)
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : PrefixPhysicalInputs P d r n,
      entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val) :
    let pairCells := btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc
    let midpoint := fun (j : Fin P) (i : Fin Q) =>
      (((trace.poolValues hlen hpool ((j, i), false)).val : ℝ) +
        (trace.poolValues hlen hpool ((j, i), true)).val) / 2
    Function.Injective pairCells ∧
    (∀ x, entry a (pairCells x) = (trace.poolValues hlen hpool x).val) ∧
    Set.PairwiseDisjoint (Set.univ : Set (Fin P)) (physicalPairStageCells pairCells) ∧
    (∀ j, (physicalPairStageCells pairCells j).card = 2 * Q) ∧
    (∀ j, (∑ c ∈ physicalPairStageCells pairCells j, (entry a c : ℝ)) =
      2 * ∑ i, midpoint j i) ∧
    (∀ S : Finset (Fin P), S.biUnion (physicalPairStageCells pairCells) ⊆
      Finset.univ.image (btGrowingOffsetCells offset hoff hs choice rows cols hr hc)) := by
  classical
  dsimp only
  let eqv := prefixPhysicalInputEquiv (P := P) hfit hdiag hexact
  let pairCells := btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc
  have hentry (x : (Fin P × Fin Q) × Bool) :
      entry a (pairCells x) = (trace.poolValues hlen hpool x).val := by
    have h := hplaced (eqv.symm x)
    have he : prefixPhysicalInput hfit hdiag (eqv.symm x) = x := eqv.apply_symm_apply x
    rw [he] at h
    exact h
  have hcellinj : Function.Injective pairCells := by
    intro x y h
    apply trace.poolValues_injective hlen hpool
    apply Subtype.ext
    exact (hentry x).symm.trans ((congrArg (entry a) h).trans (hentry y))
  have htotals := physical_pair_stage_cells_disjoint_card pairCells hcellinj
  refine ⟨hcellinj, hentry, htotals.1, htotals.2, ?_, ?_⟩
  · intro j
    apply physical_pair_stage_sum_midpoints a pairCells hcellinj
      (fun j i => (((trace.poolValues hlen hpool ((j, i), false)).val : ℝ) +
        (trace.poolValues hlen hpool ((j, i), true)).val) / 2)
    intro i k
    rw [hentry, hentry]
  · intro S c hc'
    obtain ⟨j, hj, hc'⟩ := Finset.mem_biUnion.mp hc'
    obtain ⟨⟨i, side⟩, _, rfl⟩ := Finset.mem_image.mp hc'
    exact Finset.mem_image.mpr ⟨eqv.symm ((j, i), side), Finset.mem_univ _, rfl⟩

end
end Sude
