import Sude.FWFullReservedSignedCancellation
import Sude.FWRoleCellOccupancy

/-! Apply signed cancellation to supplied stages on the actual FW role and
full-reservation geometry. No theta witness or numerical bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- The reviewed FW geometry supplies role inclusion and full cardinality;
the supplied same-square stage data, positive unused count, and line-capacity
condition remain explicit. No restriction to particular values of `q` is used. -/
theorem fw_geometry_stages_signed_cancellation {n P : ℕ} {I : Type*} [DecidableEq I]
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n * n)) (stages : Finset I) (cells : I → Finset (Cell n))
    (d q : ℕ) (mean : I → ℝ)
    (hdis : Set.PairwiseDisjoint (↑stages : Set I) cells)
    (hcard : ∀ j ∈ stages, (cells j).card = 2 * d * (n + 8))
    (hsum : ∀ j ∈ stages,
      (∑ z ∈ cells j, (entry a z : ℝ)) = (2 * d * (n + 8) : ℕ) * mean j)
    (hstage : stages.biUnion cells ⊆
      fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
        Finset.univ.image (btGrowingOffsetCells
          (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc))
    (hfull : (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))).card < n * n)
    (hline : 12 * (5 + 16 + 3 * (n / 450) + P) + q ≤ n) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j ∈ stages, (mean j - μ)
    let O : ℝ := (∑ z ∈ roles \ stages.biUnion cells, (entry a z : ℝ)) -
      ((roles \ stages.biUnion cells).card : ℝ) * μ
    let D : ℝ := (∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ) * μ
    let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
    let k : ℝ := (n - 12 * (5 + 16 + 3 * (n / 450) + P) - q : ℕ)
    2 * (d : ℝ) * A + k * (centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ) =
      (2 * (d : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) -
        96 * ((238 : ℝ) - P) - 8 * n) - k * (O + D) / N := by
  dsimp only
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hocc
  exact fw_full_reserved_stages_signed_cancellation hP a _ _ stages cells d q mean
    hdis hcard hsum hstage hocc.1 hocc.2.2.2.2.2.2.1 hfull hline

end
end Sude
