import Sude.FWGrowthOrdinaryRowColumnMass
import Sude.FWGrowthJointIndex
import Sude.PrefixPhysicalSlotGeometry

/-! Each actual growth pair is either protected in the rectangle reservation
or is exactly one joint-network pair. No switch or reference is constructed. -/
namespace Sude
noncomputable section

/-- Exact physical coverage of every growth pair by the protected rectangle,
row network, or transposed column network, preserving endpoint sides. -/
theorem fw_growth_pair_network_coverage {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (j : Fin P) (i : Fin (6*(n+8))) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    (∀ side, cells ((j,i),side) ∈ packedRectangleSupport hs choice) ∨
    (∃ k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n,
      ∀ side, cells ((j,i),side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k side) ∨
    (∃ k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n,
      ∀ side, cells ((j,i),side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k side).swap) := by
  classical
  dsimp only
  let hf : (4*6)*2 + 2*(3*n) ≤ 6*(n+8) := by omega
  let hd : (4*6)*2 ≤ 6*(n+8) := by omega
  let he : (4*6)*2 + 2*(3*n) = 6*(n+8) := by omega
  obtain ⟨p, hp⟩ := (prefixStagePairSlot_bijective (d := 6) (layers := 3) (n := n) hf hd he).2 i
  subst i
  cases p with
  | inl v =>
    rcases v with ⟨rect, pair⟩
    left
    intro side
    change btGrowingOffsetPairCells hf hd he offset hoff hs choice gr gc hgr hgc
      ((j, prefixDiagonalPairIndex hd (rect,pair)),side) ∈ _
    rw [fw_growth_offset_rectangle_cell]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  | inr v =>
    rcases v with ⟨network,k,e⟩
    fin_cases network
    · right; left
      refine ⟨(fwGrowthJointLayerIndex br sr wr gr hgr j k, e), ?_⟩
      intro side
      change btGrowingOffsetPairCells hf hd he offset hoff hs choice gr gc hgr hgc
        ((j,prefixOrdinaryPairIndex hf (0,k,e)),side) = _
      rw [fw_growth_ordinary_row_cell]
      simp only [layerPairSlot, LayerPacking.sequenceCell, fwGrowthJointLayerIndex_get]
      rfl
    · right; right
      refine ⟨(fwGrowthJointLayerIndex bc sc wc gc hgc j k, e), ?_⟩
      intro side
      change btGrowingOffsetPairCells hf hd he offset hoff hs choice gr gc hgr hgc
        ((j,prefixOrdinaryPairIndex hf (1,k,e)),side) = _
      rw [fw_growth_ordinary_column_cell]
      simp only [layerPairSlot, LayerPacking.sequenceCell, fwGrowthJointLayerIndex_get]
      rfl

end
end Sude
