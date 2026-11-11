import Sude.FWEarlyReferenceMidpointScores

/-! Retain supplied early-family midpoint concentration bounds on one fresh
reference, with their original source means. No ordered-gap invoice follows. -/
namespace Sude
noncomputable section

/-- Under exact same-reference pair-sum preservation, the supplied seed,
bridge and wide midpoint-score bounds hold simultaneously on the fresh square.
Seed means retain `grown` and bridge/wide means retain the distinct `source`.
This says nothing about later flow switches or complete physical line sums. -/
theorem fw_early_reference_midpoint_bounds {n L : ℕ}
    (hrect : 5*(4*6) ≤ L)
    (hseed : 5*(4*6) + 16*(4*6) ≤ L)
    (hwide : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (grown source ordered fresh : Cell n ≃ Fin (n*n))
    (ω : Fin 16 → Equiv.Perm (Fin (6*(n+8))))
    (hplaced : ∀ j i side,
      entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),side)) =
        entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,ω j i),side)))
    (hfixed : ∀ c ∈ packedRectangleSupport hs choice, entry fresh c = entry ordered c)
    (hrow : ∀ k, entry fresh (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false) +
        entry fresh (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true) =
      entry ordered (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false) +
        entry ordered (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true))
    (hcol : ∀ k, entry fresh ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap) +
        entry fresh ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap) =
      entry ordered ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap) +
        entry ordered ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap))
    (Bseed Bbridge Bwide : ℝ)
    (hseedBound : let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      let line := fun l : Fin ((n+n)+2) => fun c => c ∈ physicalAllLineCells l
      let weights := fun l j i => physicalPairLineWeight seed (line l) (j,i)
      let values := fun j i => (((entry grown (seed ((j,i),false)) : ℝ) +
        entry grown (seed ((j,i),true))) / 2)
      ∀ l, |stageLineCentered (fun _ _ => Finset.univ) weights values l ω| ≤ Bseed)
    (hbridgeBound : ∀ l : Fin ((n+n)+2),
      |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun c => c ∈ physicalAllLineCells l) source ordered| < Bbridge)
    (hwideBound : ∀ l : Fin ((n+n)+2),
      |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun c => c ∈ physicalAllLineCells l) source ordered| < Bwide) :
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let line := fun l : Fin ((n+n)+2) => fun c => c ∈ physicalAllLineCells l
    let weights := fun l j i => physicalPairLineWeight seed (line l) (j,i)
    let values := fun j i => (((entry grown (seed ((j,i),false)) : ℝ) +
      entry grown (seed ((j,i),true))) / 2)
    ∀ l : Fin ((n+n)+2),
      |(∑ j, ∑ i, weights l j i *
          (((((entry fresh (seed ((j,i),false)) : ℝ) + entry fresh (seed ((j,i),true))) / 2)) -
            ((∑ q, values j q) / (6*(n+8) : ℕ))))| ≤ Bseed ∧
      |doubleBlockActualCenteredScore bridge (line l) source fresh| < Bbridge ∧
      |doubleBlockActualCenteredScore wide (line l) source fresh| < Bwide := by
  classical
  dsimp only
  have he := fw_early_reference_midpoint_scores hrect hseed hwide hs choice br sr wr gr bc sc wc gc
    hbr hbc hsr hsc hwr hwc grown source ordered fresh ω hplaced hfixed hrow hcol
  intro l
  obtain ⟨hseedEq, hbridgeEq, hwideEq⟩ := he l
  refine ⟨?_, ?_, ?_⟩
  · rw [← hseedEq]
    exact hseedBound l
  · rw [hbridgeEq]
    exact hbridgeBound l
  · rw [hwideEq]
    exact hwideBound l

end
end Sude
