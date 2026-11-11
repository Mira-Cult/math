import Sude.FWGrowthDiagonalBounds
import Sude.FWGrowthPackedSuffix
import Sude.FWGrowthEarlyRolePreservation

/-! Conditional same-square growth allocation with the other FW roles fixed.
The source of the bridge/wide centered scores remains explicitly supplied. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

/-- Under the actual joint packing and supplied trace placement, the growth
allocation retains the complete early-role endpoints and scores on the same
square. The growth and diagonal bounds use one selected allocation. -/
theorem fw_growth_protected_diagonal_bounds {n : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n) (hn : 3 ≤ n)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X/6) stages)
    (hP : stages.length ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (hgr : gr.length = stages.length*3) (hgc : gc.length = stages.length*3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (hchoice : ∀ j rect, choice (btGrowingOffsetRectangle
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff (finProdFinEquiv (j,rect))) = decide (rect.val < 12))
    (source a : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry a (btGrowingOffsetCells (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput (by omega) (by omega) x)).val) :
    let offset := 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)
    let L := fwJointRectangleCount n 254
    let rows := gr
    let cols := gc
    let hr := hgr
    let hc := hgc
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    ∃ (T U V : Fin stages.length → Finset ℕ)
      (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8)))) (a' : Cell n ≃ Fin (n*n)),
      (∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
        V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
        (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24) ∧
      (∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
        (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
        (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j) ∧
      (∀ x, entry a' (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω x)).val) ∧
      (∀ c, c ∉ Set.range cells → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a (cells ((j,x.1),x.2)))) ∧
      (∀ j i, entry a' (cells ((j,i),true)) =
        entry a' (cells ((j,i),false)) + (stages.get j).gap) ∧
      ((∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ mainCells n), (entry a' c : ℝ)) =
        (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) -
          6 * ∑ j, ((stages.get j).gap : ℝ)) ∧
      ((∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ antiCells n), (entry a' c : ℝ)) =
        (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) -
          6 * ∑ j, ((stages.get j).gap : ℝ)) ∧
      let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6 * (n+8) : ℕ)
      let E1 := (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
      let D2 := (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
      let E2 := (∑ j, ∑ p ∈ T j ∪ U j, growthStageMidpoint (stages.get j) p) - (24 : ℝ) * ∑ j, μ j
      let E3 := (∑ j, ∑ p ∈ (T j ∪ U j) ∪ V j, growthStageMidpoint (stages.get j) p) - (48 : ℝ) * ∑ j, μ j
      |E1| ≤ (X/6)/2 ∧ |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*(X/6) ∧
        |E2| ≤ ((n+5 : ℝ)/(n+6))*(X/6) ∧ |E3| ≤ (3/2:ℝ)*(X/6) ∧
        (0 < X/6 → |E3| < (3/2:ℝ)*(X/6)) ∧
        |(∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ mainCells n), (entry a' c : ℝ)) -
          ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤ (X/6)/2 ∧
        |(∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ antiCells n), (entry a' c : ℝ)) -
          ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤ ((n+8 : ℝ)/(2*(n+6)))*(X/6) ∧
        (∀ x, entry a' (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) =
          entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) ∧
        (∀ x, entry a' (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x) =
          entry a (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x)) ∧
        (∀ x, entry a' (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x) =
          entry a (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x)) ∧
        (∀ line, doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) line source a' =
          doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) line source a) ∧
        (∀ line, doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) line source a' =
          doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) line source a) := by
  classical
  dsimp only
  obtain ⟨T,U,V,ω,a',hsel,hmap,hperm,hfix,hstage,hgap,hmain,hanti,hE1,hD2,hE2,hE3,hE3s,hbmain,hbanti⟩ :=
    fw_growth_allocated_diagonal_bounds trace hpool hn X hX hnarrow _ hoff hs choice gr gc hgr hgc
      _ _ (LayerPacking.packed_layers_suffix _ _ hrows) (LayerPacking.packed_layers_suffix _ _ hcols)
      (by omega) hchoice a hplaced
  obtain ⟨hsf,hbf,hwf,hbs,hws⟩ := fw_growth_reallocation_preserves_early_roles
    hP hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    hrows hcols source a a' hfix
  exact ⟨T,U,V,ω,a',hsel,hmap,hperm,hfix,hstage,hgap,hmain,hanti,hE1,hD2,hE2,hE3,hE3s,hbmain,hbanti,hsf,hbf,hwf,hbs,hws⟩

end
end Sude
