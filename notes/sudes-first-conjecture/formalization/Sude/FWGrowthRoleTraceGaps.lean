import Sude.BTGrowingOffsetPhysical

/-! Transfer the stage-specific ordinary-network gap equations from an
installed growing trace to a square preserving the same physical role cells.
No network, grid, or square is constructed here. -/
namespace Sude
noncomputable section

/-- On both actual ordinary networks, every pair on a trace stage keeps that
stage's gap when its physical role cells are preserved. The same placement,
trace, and role map are used throughout. -/
theorem bt_growing_preserved_role_network_gaps
    {g Q n d r L : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (offset : ℕ) (hoff : offset + stages.length * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length * r) (hc : cols.length = stages.length * r)
    (old new : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length d r n,
      entry old (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput hfit hdiag x)).val)
    (hfixed : ∀ x : PrefixPhysicalInputs stages.length d r n,
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        entry old (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x)) :
    (∀ (i : Fin (stages.length * r)) (e : Fin n),
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) ∧
    (∀ (i : Fin (stages.length * r)) (e : Fin n),
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) := by
  have hnew (x : PrefixPhysicalInputs stages.length d r n) :
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput hfit hdiag x)).val :=
    (hfixed x).trans (hplaced x)
  constructor
  · intro i e
    rw [hnew (Sum.inr (Sum.inl (i, (e, true)))), hnew (Sum.inr (Sum.inl (i, (e, false))))]
    exact variable_prefixNetwork_pair_gap _ hfit rfl 0 _ (trace.poolValues_gap rfl hpool) i e
  · intro i e
    rw [hnew (Sum.inr (Sum.inr (i, (e, true)))), hnew (Sum.inr (Sum.inr (i, (e, false))))]
    exact variable_prefixNetwork_pair_gap _ hfit rfl 1 _ (trace.poolValues_gap rfl hpool) i e

end
end Sude
