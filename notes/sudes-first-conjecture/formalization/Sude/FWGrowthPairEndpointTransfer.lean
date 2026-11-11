import Sude.FWGrowthPairNetworkCoverage
import Sude.MarkedPairEndpointTransfer

/-! Same-reference growth-pair endpoint and gap-magnitude transfer. The
network switch relation is supplied; no later flow output is covered. -/
namespace Sude
noncomputable section

/-- Under fixed rectangle cells and exact identity-or-reversal relations for
both joint network families on the same two squares, every actual growth pair
has the same unordered endpoint values. -/
theorem fw_growth_pair_endpoints_transfer {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (a b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ packedRectangleSupport hs choice, entry b c = entry a c)
    (hrow : ∀ k, pairEndpointSameOrSwapped a b
      (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false)
      (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true))
    (hcol : ∀ k, pairEndpointSameOrSwapped a b
      ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap)
      ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap)) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    ∀ j i, pairEndpointSameOrSwapped a b (cells ((j,i),false)) (cells ((j,i),true)) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice gr gc hgr hgc
  have hcover : ∀ z : Fin P × Fin (6*(n+8)),
      (∀ side, cells (z,side) ∈ packedRectangleSupport hs choice) ∨
      (∃ k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n,
        ∀ side, cells (z,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k side) ∨
      (∃ k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n,
        ∀ side, cells (z,side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k side).swap) := by
    rintro ⟨j,i⟩
    exact fw_growth_pair_network_coverage offset hoff hs choice br sr wr gr bc sc wc gc hgr hgc j i
  have h := marked_pair_endpoints_preserved a b (packedRectangleSupport hs choice) cells
    (fun z => layerPairSlot (((br ++ sr) ++ wr) ++ gr) z.1 z.2)
    (fun z => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) z.1 z.2).swap)
    hfixed hrow hcol hcover
  exact fun j i => h (j,i)

/-- If the input placement has one specified nonnegative gap per growth
stage, the same-reference signed gaps have that magnitude; either sign may
occur because the endpoints may be reversed. -/
theorem fw_growth_pair_gap_magnitude_transfer {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (a b : Cell n ≃ Fin (n*n)) (gap : Fin P → ℕ)
    (hgap : ∀ j i,
      entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),false)) + gap j)
    (hpair : ∀ j i, pairEndpointSameOrSwapped a b
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),false))
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),true))) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    ∀ j i, |(entry b (cells ((j,i),true)) : ℤ) - entry b (cells ((j,i),false))| = (gap j : ℤ) := by
  dsimp only
  intro j i
  have hm := pair_endpoint_gap_magnitude_preserved a b _ _ (hpair j i)
  rw [hm]
  have hg : (entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc ((j,i),true)) : ℤ) -
      entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc ((j,i),false)) = (gap j : ℤ) := by
    have hcast : (entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),true)) : ℤ) =
      (entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),false)) : ℤ) + (gap j : ℤ) := by
      exact_mod_cast hgap j i
    omega
  rw [hg]
  exact abs_of_nonneg (Int.natCast_nonneg _)

end
end Sude
