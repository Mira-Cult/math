import Sude.FWSeedPrescribedDiagonalBound
import Sude.FWSeedReferenceDiagonalSupport
import Sude.FWJointPackedOccupancy

/-! The seed diagonal invoice on the physical rectangle support, transported
to the reference of the very same supplied network. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

theorem fw_seed_reference_support_sum {n L : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (labels : Finset (Fin L)) (line : Finset (Cell n))
    (a b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ z ∈ packedRectangleSupport hs choice, entry a z = entry b z) :
    (∑ z ∈ activeRectangleSupport hs choice labels ∩ line, (entry a z : ℝ)) =
    (∑ z ∈ activeRectangleSupport hs choice labels ∩ line, (entry b z : ℝ)) := by
  classical
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : z ∈ activeRectangleSupport hs choice labels := (Finset.mem_inter.mp hz).1
  exact_mod_cast hfixed z (active_rectangle_support_subset_packed hs choice labels hz')

theorem fw_seed_reference_first_band_diagonal_difference {n : ℕ}
    (lower : RSIndexLower) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hL : 3 ≤ fwJointRectangleCount n 254)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254)
      (fwBridgeSeedRectangleChoice hrect hseed otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles) :
    let support := activeRectangleSupport f.hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
      (Finset.univ.image (fwSeedRectangle f.hseedrect))
    |(∑ z ∈ support ∩ mainCells n, (entry oldReference z : ℝ)) -
      (∑ z ∈ support ∩ antiCells n, (entry oldReference z : ℝ))| ≤ 3 * (poolMaximum n : ℝ) := by
  classical
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let support := activeRectangleSupport f.hs choice (Finset.univ.image (fwSeedRectangle f.hseedrect))
  have hsum (line : Finset (Cell n)) :
      (∑ z ∈ support ∩ line, (entry oldReference z : ℝ)) =
      (∑ z ∈ support ∩ line, (entry f.ordered z : ℝ)) :=
    fw_seed_reference_support_sum f.hs choice (Finset.univ.image (fwSeedRectangle f.hseedrect))
      line oldReference f.ordered net.rectangle_fixed
  have hb := fw_seed_prescribed_first_band_diagonal_difference lower hnlo hnhi hrect hseed hL otherChoice f
  dsimp only at hb
  rw [fw_seed_reference_diagonal_support choice f (mainCells n)
    (by intro z hz; exact Finset.mem_union_left _ hz),
    fw_seed_reference_diagonal_support choice f (antiCells n)
    (by intro z hz; exact Finset.mem_union_right _ hz)] at hb
  change |(∑ z ∈ support ∩ mainCells n, (entry oldReference z : ℝ)) -
    (∑ z ∈ support ∩ antiCells n, (entry oldReference z : ℝ))| ≤ _
  rw [hsum (mainCells n), hsum (antiCells n)]
  exact hb

end
end Sude
