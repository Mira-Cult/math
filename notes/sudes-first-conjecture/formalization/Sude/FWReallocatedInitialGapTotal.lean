import Sude.FWReallocatedSeedEdgeGap
import Sude.FWPhysicalGridGapTotal

/-! The actual seed and growth edge-gap totals agree with the supplied
trace radius on the same square. No placement or crossing is constructed. -/
namespace Sude
noncomputable section

/-- Retained seed gap two and installed growth role equations identify every
physical edge's initial total with the exact last radius of a trace starting
at 32, including when the growth stage list is empty. -/
theorem fw_reallocated_initial_gap_total {n L Q : ℕ} {initial final : Finset ℕ}
    {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (new : Cell n ≃ Fin (n*n))
    (hseedgap : ∀ j i, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) :
    ∀ (edge : Fin 3 × Fin n) (network : Bool),
      (∑ i, fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network) (Sum.inl i)) +
      (∑ i, fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network) (Sum.inr i)) = last := by
  intro edge network
  exact fw_physical_trace_gap_total trace new (fwSeedEdgeCells sr sc hsr hsc edge network)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
    (fw_reallocated_seed_edge_gap hseed hs choice sr sc hsr hsc new hseedgap edge network)
    (fw_growth_edge_gap_of_installation offset hoff hs choice gr gc hgr hgc new hrow hcol edge network)

end
end Sude
