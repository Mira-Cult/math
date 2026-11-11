import Sude.FWGrowthAllLineMidpointWitness
import Sude.FWGrowthSameSquareDiagonalBounds
import Sude.FWGrowthPackedSuffix
import Sude.FWGrowthEarlyRolePreservation

/-! One growth reallocation with row/column midpoint and selected diagonal
bounds, protecting the earlier seed, bridge, and wide roles. This is not a
complete-line theorem and has explicit trace and packing assumptions. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

/-- Apply the row/column growth allocator and diagonal invoice to the same
final square, retaining the protected early roles and their source scores. -/
theorem fw_growth_protected_all_line_midpoint_bounds {n : ℕ} {initial final : Finset ℕ}
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
        (∀ r : Fin n,
          |∑ s : Fin stages.length × Fin (6*(n+8)),
            physicalPairLineWeight cells (fun c => c.1 = r) s *
              ((((entry a' (cells (s,true)) : ℝ) + entry a' (cells (s,false))) / 2) - μ s.1)| ≤
            (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) ∧
        (∀ c : Fin n,
          |∑ s : Fin stages.length × Fin (6*(n+8)),
            physicalPairLineWeight cells (fun q => q.2 = c) s *
              ((((entry a' (cells (s,true)) : ℝ) + entry a' (cells (s,false))) / 2) - μ s.1)| ≤
            (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) ∧
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
  have hrows' : LayerPacking.PackedLayers (packedRectangleSupport hs choice) gr :=
    LayerPacking.packed_layers_suffix _ _ hrows
  have hcols' : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) gc :=
    LayerPacking.packed_layers_suffix _ _ hcols
  obtain ⟨T,U,V,ω,a',hsel,hmap,hperm,hfix,hstage,hgap,hbudget,hrow,hcol⟩ :=
    fw_growth_all_line_midpoint_witness trace hpool hn X hX hnarrow _ hoff hs choice gr gc hgr hgc
      _ _ hrows' hcols' a hplaced
  obtain ⟨hE1,hD2,hE2,hE3,hE3s⟩ := hbudget
  obtain ⟨hmain,hanti,hbmain,hbanti⟩ := fw_growth_same_square_diagonal_bounds
    trace hpool _ hoff hs (by omega) choice gr gc hgr hgc _ _ hrows' hcols' hchoice a' ω T U X
    (fun j => (hmap j).1) (fun j => (hmap j).2.1) hperm hE1 hD2
  obtain ⟨hsf,hbf,hwf,hbs,hws⟩ := fw_growth_reallocation_preserves_early_roles
    hP hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    hrows hcols source a a' hfix
  exact ⟨T,U,V,ω,a',hsel,hmap,hperm,hfix,hstage,hgap,hmain,hanti,hE1,hD2,hE2,hE3,hE3s,
    hbmain,hbanti,hrow,hcol,hsf,hbf,hwf,hbs,hws⟩

end
end Sude
