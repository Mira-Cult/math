import Sude.FWGrowthPairNetworkCoverage
import Sude.MarkedPairMidpointTransfer

/-! Transfer actual growth-pair midpoints through a supplied reference. This
uses explicit network pair-sum preservation; it does not construct switches. -/
namespace Sude
noncomputable section

/-- If both endpoints of every joint row and column network pair retain their
sum and rectangle cells stay fixed, every actual growth-pair midpoint is
unchanged. The placements `a` and `b` are the SAME two supplied squares as in
the hypotheses. This does not derive pair-sum preservation from an invoice or
from equality of value images. -/
theorem fw_growth_pair_midpoint_transfer {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
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
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    ∀ j i, (((entry b (cells ((j,i),false)) : ℝ) + entry b (cells ((j,i),true))) / 2) =
      (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice gr gc hgr hgc
  have hc : ∀ z : Fin P × Fin (6*(n+8)),
      (∀ side, cells (z,side) ∈ packedRectangleSupport hs choice) ∨
      (∃ (k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n) (rev : Bool), ∀ side,
        cells (z,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k (if rev then !side else side)) ∨
      (∃ (k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n) (rev : Bool), ∀ side,
        cells (z,side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k (if rev then !side else side)).swap) := by
    rintro ⟨j,i⟩
    rcases fw_growth_pair_network_coverage offset hoff hs choice br sr wr gr bc sc wc gc hgr hgc j i with h | h | h
    · exact Or.inl h
    · obtain ⟨k,hk⟩ := h
      exact Or.inr (Or.inl ⟨k,false,by simpa using hk⟩)
    · obtain ⟨k,hk⟩ := h
      exact Or.inr (Or.inr ⟨k,false,by simpa using hk⟩)
  have hm := marked_pair_midpoint_preserved a b (packedRectangleSupport hs choice) cells
    (fun z => layerPairSlot (((br ++ sr) ++ wr) ++ gr) z.1 z.2)
    (fun z => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) z.1 z.2).swap)
    hfixed hrow hcol hc
  exact fun j i => hm (j,i)

/-- Fixed weights and the same source-stage reference transfer any finite
weighted sum of the actual growth-pair midpoints. -/
theorem fw_growth_weighted_midpoints_transfer {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (a b : Cell n ≃ Fin (n*n))
    (w : Fin P × Fin (6*(n+8)) → ℝ)
    (hmid : ∀ j i,
      (((entry b (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice gr gc hgr hgc ((j,i),false)) : ℝ) +
        entry b (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice gr gc hgr hgc ((j,i),true))) / 2) =
      (((entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice gr gc hgr hgc ((j,i),false)) : ℝ) +
        entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice gr gc hgr hgc ((j,i),true))) / 2)) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    (∑ z : Fin P × Fin (6*(n+8)), w z *
      (((entry b (cells (z,false)) : ℝ) + entry b (cells (z,true))) / 2)) =
    ∑ z : Fin P × Fin (6*(n+8)), w z *
      (((entry a (cells (z,false)) : ℝ) + entry a (cells (z,true))) / 2) := by
  classical
  dsimp only
  apply Finset.sum_congr rfl
  rintro ⟨j,i⟩ _
  rw [hmid j i]

end
end Sude
