import Sude.FWBridgeWideUnmatchedRowOrientation
import Sude.MarkedPairMidpointTransfer
import Sude.DoubleBlockScoreDecomposition

/-! Pointwise bridge-pair midpoint preservation on one supplied reference.
This does not construct centering switches or transfer through later flows. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- Every actual grouped bridge pair lies either in the protected rectangle
reservation or is one complete joint row/column layer pair. -/
theorem fw_bridge_pair_network_coverage {n L : ℕ}
    (hrect : 5*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
    (j : Fin 5) (b : Fin (3*(n+8))) (p : Fin 2) :
    let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
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
      have hcell : fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
          ((j, Fin.castLE (by omega) rect, pair),side) =
        packedRectangleCorner hs choice
          (bridgeDiagonalRectangle hrect (finProdFinEquiv (j,rect)), prefixPairCorner pair side) := by
        rw [← fw_bridge_reindexed_diagonal_cell hrect hs choice br bc hbr hbc j rect pair side]
        rw [fwPrefixToControllerPair_diagonal]
        rfl
      rw [hcell]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  | inr ne =>
    obtain ⟨network,edge⟩ := ne
    simp only [fwControllerStagePairBlock] at htag
    cases Prod.mk.inj htag with
    | intro hb hp =>
      subst b
      subst p
      fin_cases network
      · right; left
        exact ⟨(fwBridgeJointLayerIndex br sr wr gr hbr j edge.1, edge.2),
          fun side => fw_bridge_grouped_joint_row_match hrect hs choice br sr wr gr bc hbr hbc j edge.1 edge.2 side⟩
      · right; right
        exact ⟨(fwBridgeJointLayerIndex bc sc wc gc hbc j edge.1, edge.2),
          fun side => fw_bridge_grouped_joint_column_match hrect hs choice br bc sc wc gc hbr hbc j edge.1 edge.2 side⟩

/-- The same supplied original/reference squares have equal actual grouped
bridge-pair midpoints if rectangle cells are fixed and joint network pair
endpoint sums are preserved. -/
theorem fw_bridge_pair_midpoint_transfer {n L : ℕ}
    (hrect : 5*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
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
    let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    ∀ j k p, doubleBlockPairMidpoint cells b j k p = doubleBlockPairMidpoint cells a j k p := by
  classical
  dsimp only
  let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  have hc : ∀ z : Fin 5 × Fin (3*(n+8)) × Fin 2,
      (∀ side, cells (z,side) ∈ packedRectangleSupport hs choice) ∨
      (∃ (k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n) (rev : Bool), ∀ side,
        cells (z,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k (if rev then !side else side)) ∨
      (∃ (k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n) (rev : Bool), ∀ side,
        cells (z,side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k (if rev then !side else side)).swap) := by
    rintro ⟨j,k,p⟩
    rcases fw_bridge_pair_network_coverage hrect hs choice br sr wr gr bc sc wc gc hbr hbc j k p with h | h | h
    · exact Or.inl h
    · obtain ⟨z,hz⟩ := h
      exact Or.inr (Or.inl ⟨z,false,by simpa using hz⟩)
    · obtain ⟨z,hz⟩ := h
      exact Or.inr (Or.inr ⟨z,false,by simpa using hz⟩)
  have hm := marked_pair_midpoint_preserved a b (packedRectangleSupport hs choice) cells
    (fun z => layerPairSlot (((br ++ sr) ++ wr) ++ gr) z.1 z.2)
    (fun z => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) z.1 z.2).swap)
    hfixed hrow hcol hc
  exact fun j k p => hm (j,k,p)

end
end Sude
