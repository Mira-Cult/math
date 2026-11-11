import Sude.BTGrowingPhysicalStageTotals

/-! Transfer an existing offset trace placement through a square change
that fixes its actual pair cells. No grid or existence claim is made. -/

namespace Sude
noncomputable section

/-- Fixing every pair-indexed offset cell fixes every original physical role
cell. Exact capacity supplies the stage-and-side preserving equivalence. -/
theorem bt_offset_roles_fixed_of_pairs_fixed {P d r n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (offset : ℕ) (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P * r) (hc : cols.length = P * r)
    (old new : Cell n ≃ Fin (n * n))
    (hfixed : ∀ x, entry new (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc x) =
      entry old (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc x)) :
    ∀ x : PrefixPhysicalInputs P d r n,
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
      entry old (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) := by
  intro x
  have h := hfixed (prefixPhysicalInput hfit hdiag x)
  simpa only [btGrowingOffsetPairCells, prefixPhysicalInputEquiv, Equiv.ofBijective_symm_apply_apply] using h

/-- Transport an already installed trace through a square change fixing all
pair cells. This preserves the exact stage, slot, side, and role equations;
it does not construct a trace or prove a grid. -/
theorem BTGrowingTrace.offset_placement_of_pairs_fixed
    {g Q n P d r L : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (offset : ℕ) (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P * r) (hc : cols.length = P * r)
    (old new : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : PrefixPhysicalInputs P d r n,
      entry old (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val)
    (hfixed : ∀ x, entry new (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc x) =
      entry old (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc x)) :
    (∀ x : PrefixPhysicalInputs P d r n,
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val) ∧
    (∀ x, entry new (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc x) =
      (trace.poolValues hlen hpool x).val) ∧
    (∀ j : Fin P, ∀ i : Fin Q,
      entry new (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc ((j,i),true)) =
        entry new (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc ((j,i),false)) +
          (BTStageTrace.stageAt stages hlen j).gap) := by
  have hrole := bt_offset_roles_fixed_of_pairs_fixed hfit hdiag hexact offset hoff hs choice rows cols hr hc old new hfixed
  have hplacedNew : ∀ x : PrefixPhysicalInputs P d r n,
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val := by
    intro x
    exact (hrole x).trans (hplaced x)
  have hpair : ∀ x, entry new (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc x) =
      (trace.poolValues hlen hpool x).val := by
    intro x
    have h := hplacedNew ((prefixPhysicalInputEquiv (P := P) hfit hdiag hexact).symm x)
    simpa only [btGrowingOffsetPairCells, prefixPhysicalInputEquiv, Equiv.ofBijective_apply_symm_apply] using h
  refine ⟨hplacedNew, hpair, ?_⟩
  intro j i
  rw [hpair, hpair]
  exact trace.poolValues_gap hlen hpool j i

end
end Sude
