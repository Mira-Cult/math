import Sude.FWBridgeWideNetworkMatching
import Sude.MarkedPairMidpointTransfer

/-! Exact wide-pair coverage and midpoint transfer on two supplied squares.
No centering switch or later flow is constructed here. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Each actual grouped wide pair is either in the protected rectangle
reservation or is exactly a row/column joint-network pair, side for side. -/
theorem fw_wide_pair_network_coverage {n L : ℕ}
    (hwide : 5 * (4*6) + 16 * (4*6) + (3*(n/450))*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (j : Fin (3*(n/450))) (b : Fin (3*(n+8))) (p : Fin 2) :
    let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    (∀ side, cells ((j,b,p),side) ∈ packedRectangleSupport hs choice) ∨
    (∃ k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n,
      ∀ side, cells ((j,b,p),side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k side) ∨
    (∃ k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n,
      ∀ side, cells ((j,b,p),side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k side).swap) := by
  classical
  dsimp only
  obtain ⟨tag, htag⟩ := (fwControllerStagePairBlock_bijective n).2 (b,p)
  cases tag with
  | inl rp =>
    obtain ⟨rect,pair⟩ := rp
    simp only [fwControllerStagePairBlock] at htag
    cases Prod.mk.inj htag with
    | intro hb hp =>
      subst b
      subst p
      left
      intro side
      have hcell : fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
          ((j, Fin.castLE (by omega) rect, pair),side) =
        packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j,rect)), prefixPairCorner pair side) := by
        rw [← fw_wide_reindexed_diagonal_cell hwide hs choice wr wc hwr hwc j rect pair side]
        rw [fwPrefixToControllerPair_diagonal]
        rfl
      rw [hcell]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  | inr ne =>
    obtain ⟨network,edge⟩ := ne
    obtain ⟨k,e⟩ := edge
    simp only [fwControllerStagePairBlock] at htag
    cases Prod.mk.inj htag with
    | intro hb hp =>
      subst b
      subst p
      fin_cases network
      · right; left
        refine ⟨(fwWideJointLayerIndex br sr wr gr hwr j k,e), ?_⟩
        intro side
        exact fw_wide_grouped_joint_row_match hwide hs choice br sr wr gr wc hwr hwc j k e side
      · right; right
        refine ⟨(fwWideJointLayerIndex bc sc wc gc hwc j k,e), ?_⟩
        intro side
        exact fw_wide_grouped_joint_column_match hwide hs choice wr bc sc wc gc hwr hwc j k e side

/-- With protected cells fixed and every supplied joint network-pair sum
preserved, each wide-pair midpoint is identical on these same two squares.
This conclusion does not follow from global value-image equality alone. -/
theorem fw_wide_pair_midpoint_transfer {n L : ℕ}
    (hwide : 5 * (4*6) + 16 * (4*6) + (3*(n/450))*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (a b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ packedRectangleSupport hs choice, entry b c = entry a c)
    (hrow : ∀ k, entry b (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false) +
        entry b (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true) =
      entry a (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false) +
        entry a (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true))
    (hcol : ∀ k, entry b ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap) +
        entry b ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap) =
      entry a ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap) +
        entry a ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap)) :
    let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    ∀ j k p, (((entry b (cells ((j,k,p),false)) : ℝ) + entry b (cells ((j,k,p),true))) / 2) =
      (((entry a (cells ((j,k,p),false)) : ℝ) + entry a (cells ((j,k,p),true))) / 2) := by
  classical
  dsimp only
  let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  have hc : ∀ z : Fin (3*(n/450)) × Fin (3*(n+8)) × Fin 2,
      (∀ side, cells (z,side) ∈ packedRectangleSupport hs choice) ∨
      (∃ (k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n) (rev : Bool), ∀ side,
        cells (z,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k (if rev then !side else side)) ∨
      (∃ (k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n) (rev : Bool), ∀ side,
        cells (z,side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k (if rev then !side else side)).swap) := by
    rintro ⟨j,k,p⟩
    rcases fw_wide_pair_network_coverage hwide hs choice br sr wr gr bc sc wc gc hwr hwc j k p with h | h | h
    · exact Or.inl h
    · obtain ⟨t,ht⟩ := h
      exact Or.inr (Or.inl ⟨t,false,by simpa using ht⟩)
    · obtain ⟨t,ht⟩ := h
      exact Or.inr (Or.inr ⟨t,false,by simpa using ht⟩)
  have hm := marked_pair_midpoint_preserved a b (packedRectangleSupport hs choice) cells
    (fun z => layerPairSlot (((br ++ sr) ++ wr) ++ gr) z.1 z.2)
    (fun z => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) z.1 z.2).swap)
    hfixed hrow hcol hc
  exact fun j k p => hm (j,k,p)

end
end Sude
