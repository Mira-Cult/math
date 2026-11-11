import Sude.FWFourFamilyLineComplementSplit
import Sude.FWFourFamilyWeightedStageReindex
import Sude.FWBridgeWideOrderedMeanScore

/-! Assemble a supplied same-square bridge/wide midpoint invoice with the
seed/growth component bounds. The geometric spare and free-cell sums remain
explicit. No free-cell estimate, total gate, diagonal or later-flow claim. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

/-- Four absolute component errors combine with one supplied midpoint invoice. -/
theorem reserved_midpoint_component_arithmetic
    (R sb sw bb bw S bs G bg spare free E B W U V : ℝ)
    (hcore : |R - ((sb + bb) + (sw + bw) + S + G + spare + free)| ≤ E)
    (hsb : |sb| ≤ B) (hsw : |sw| ≤ W) (hs : |S-bs| ≤ U) (hg : |G-bg| ≤ V) :
    |R - (bb + bs + bw + bg + spare + free)| ≤ E + B + W + U + V := by
  apply abs_le.mpr
  have a := abs_le.mp hcore
  have b := abs_le.mp hsb
  have c := abs_le.mp hsw
  have d := abs_le.mp hs
  have e := abs_le.mp hg
  constructor <;> linarith

/-- A conditional line invoice for the actual four-family physical geometry.
`R` may be a row or column sum of the same reference square. The supplied
`hcore` is the bridge/wide midpoint comparison on the ordered square, and
`hseed`/`hgrowth` are the seed/growth physical component comparisons on that
same square. Their construction is separate and all four error bounds remain
explicit. -/
theorem fw_reserved_midpoint_component_assembly {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseedrect : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (source ordered : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : Fin 5 → Fin (3 * (n + 8)) → Bool)
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (sw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → Bool)
    (hbridge : ∀ j b p side, entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),side)) =
      entry source (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,πb j b,doubleBlockPairSwap (sb j b) p),side)))
    (hwideEntry : ∀ j b p side, entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),side)) =
      entry source (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,πw j b,doubleBlockPairSwap (sw j b) p),side)))
    (line : Finset (Cell n)) (R E B W U V : ℝ)
    (mean : FWFourStageIndex n P → ℝ)
    (hmean : ∀ j, mean j =
      (∑ i, (((entry ordered ((fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P) ((j,i),false)) : ℝ) +
        entry ordered ((fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
          br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P) ((j,i),true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ))
    (hcore : let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
      let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
      |R - ((doubleBlockActualCenteredScore bridge (fun z => z ∈ line) source ordered +
        (∑ j, ∑ b, doubleBlockLineWeight bridge (fun z => z ∈ line) j b * doubleStageMidpointMean bridge source j)) +
       (doubleBlockActualCenteredScore wide (fun z => z ∈ line) source ordered +
        (∑ j, ∑ b, doubleBlockLineWeight wide (fun z => z ∈ line) j b * doubleStageMidpointMean wide source j)) +
       (∑ z ∈ line \ (Finset.univ.image bridge ∪ Finset.univ.image wide), (entry ordered z : ℝ)))| ≤ E)
    (hB : |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ line) source ordered| ≤ B)
    (hW : |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ line) source ordered| ≤ W)
    (hseed :
      let seed := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
      |(∑ z ∈ line ∩ Finset.univ.image seed, (entry ordered z : ℝ)) -
        (∑ j : Fin 16, ∑ i : Fin (6*(n+8)), physicalPairLineWeight seed (fun z => z ∈ line) (j,i) *
          mean (Sum.inl (Sum.inl (Sum.inr j))))| ≤ U)
    (hgrowth :
      let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
      |(∑ z ∈ line ∩ Finset.univ.image growth, (entry ordered z : ℝ)) -
        (∑ j : Fin P, ∑ i : Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z ∈ line) (j,i) * mean (Sum.inr j))| ≤ V) :
    let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let roles := fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    |R - ((∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
      physicalPairLineWeight cells (fun z => z ∈ line) (j,i) * mean j) +
      (∑ z ∈ line ∩ (full \ roles), (entry ordered z : ℝ)) +
      (∑ z ∈ line \ full, (entry ordered z : ℝ)))| ≤ E + B + W + U + V := by
  classical
  dsimp only at hcore hseed hgrowth ⊢
  let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  have hsplit := fw_physical_four_family_line_complement_split hP hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols full (by rfl : _ ⊆ full)
    line (fun z => (entry ordered z : ℝ))
  dsimp only at hsplit
  rw [hsplit] at hcore
  have hg := fw_four_family_weighted_stage_reindex hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc (fun z => z ∈ line) mean
  dsimp only at hg
  have hp := fw_four_family_bridge_wide_means_preserved hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc source ordered πb sb πw sw hbridge hwideEntry
  have ho := fw_four_family_bridge_wide_grouped_means hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc source
  dsimp only at hp ho
  have hmB (j : Fin 5) : doubleStageMidpointMean (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) source j =
      mean (Sum.inl (Sum.inl (Sum.inl j))) := (ho.1 j).symm.trans ((hp.1 j).symm.trans (hmean _).symm)
  have hmW (j : Fin (3*(n/450))) : doubleStageMidpointMean (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) source j =
      mean (Sum.inl (Sum.inr j)) := (ho.2 j).symm.trans ((hp.2 j).symm.trans (hmean _).symm)
  simp_rw [← hmB, ← hmW] at hg
  rw [hg]
  apply abs_le.mpr
  have ha := abs_le.mp hcore
  have hb := abs_le.mp hB
  have hc := abs_le.mp hW
  have hd := abs_le.mp hseed
  have he := abs_le.mp hgrowth
  constructor <;> linarith

end
end Sude
