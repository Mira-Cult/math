import Sude.BTGrowingPhysicalStageTotals
import Sude.StagePairReallocation

/-! Actual growing-trace placement after a supplied stagewise pair permutation.
The selected values and endpoints move together; no balancing permutation is
constructed here. -/
namespace Sude
noncomputable section

/-- Realize any supplied independent within-stage permutation on the same
exact-pool square, carry the trace placement through that permutation, fix
all cells outside the growth image, and preserve each original stage's
endpoint set and common gap. -/
theorem bt_growing_permuted_placement
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
        (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val)
    (ω : Fin P → Equiv.Perm (Fin Q)) :
    let cells := btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ x, entry a' (cells x) =
        (trace.poolValues hlen hpool (stagePairPermutation ω x)).val) ∧
      (∀ x : PrefixPhysicalInputs P d r n,
        entry a' (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
          (trace.poolValues hlen hpool (stagePairPermutation ω (prefixPhysicalInput hfit hdiag x))).val) ∧
      (∀ c, c ∉ Set.range cells → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : Fin Q × Bool =>
        entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin Q × Bool =>
        entry a (cells ((j,x.1),x.2)))) ∧
      (∀ j i, entry a' (cells ((j,i),true)) =
        entry a' (cells ((j,i),false)) + (BTStageTrace.stageAt stages hlen j).gap) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc
  let e := prefixPhysicalInputEquiv (P := P) hfit hdiag hexact
  have hdata := bt_growing_physical_stage_totals trace hlen hpool hfit hdiag hexact
    offset hoff hs choice rows cols hr hc a hplaced
  have hinj : Function.Injective cells := hdata.1
  have hold : ∀ x, entry a (cells x) = (trace.poolValues hlen hpool x).val := hdata.2.1
  obtain ⟨a', hperm, hfix, hstage, hgap⟩ := reallocate_existing_stage_pairs a cells hinj ω
  have hnew : ∀ x, entry a' (cells x) =
      (trace.poolValues hlen hpool (stagePairPermutation ω x)).val := by
    rintro ⟨⟨j,i⟩,side⟩
    rw [hperm, hold]
    rfl
  refine ⟨a', hnew, ?_, hfix, hstage, ?_⟩
  · intro x
    have hx : cells (prefixPhysicalInput hfit hdiag x) =
        btGrowingOffsetCells offset hoff hs choice rows cols hr hc x := by
      change btGrowingOffsetCells offset hoff hs choice rows cols hr hc
        (e.symm (e x)) = _
      rw [e.symm_apply_apply]
    rw [← hx, hnew]
  · intro j i
    rw [hnew, hnew]
    exact trace.poolValues_gap hlen hpool j (ω j i)

end
end Sude
