import Sude.FWThetaAllFamilyMidpointReference

/-! Transfer theta-style bridge and wide paired natural-gap invoices from the
reallocated square to the same growth-final square, using supplied equality of
every actual endpoint. No switch, completion, flow or gap-existence is inferred. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- The destination block keeps its stage-permuted source gap on every pair;
all equalities refer to the same supplied `new` and `final` squares. -/
theorem fw_growth_final_paired_gap_transfer {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc wr wc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (new final : Cell n ≃ Fin (n*n))
    (hfixedb : ∀ x, entry final (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x))
    (hfixedw : ∀ x, entry final (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x))
    (hgapb : ∀ j k p,
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,k,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,k,p),false)) +
        ((fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).high₁ -
          (fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).low₁))
    (hgapw : ∀ j k p,
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),false)) +
        ((blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j k)))).high₁ -
          (blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j k)))).low₁)) :
    (∀ j k p,
      entry final (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,k,p),true)) =
      entry final (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,k,p),false)) +
        ((fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).high₁ -
          (fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).low₁)) ∧
    (∀ j k p,
      entry final (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),true)) =
      entry final (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),false)) +
        ((blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j k)))).high₁ -
          (blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j k)))).low₁)) := by
  constructor
  · intro j k p
    rw [hfixedb ((j,k,p),true), hfixedb ((j,k,p),false)]
    exact hgapb j k p
  · intro j k p
    rw [hfixedw ((j,k,p),true), hfixedw ((j,k,p),false)]
    exact hgapw j k p

end
end Sude
