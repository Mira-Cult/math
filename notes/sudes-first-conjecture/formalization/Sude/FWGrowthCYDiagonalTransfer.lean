import Sude.FWThetaGrowthDiagonalWitness
import Sude.FWThetaNetworkWitness
import Sude.FWThetaFamilyDQRFInputs
import Sude.FWRoleSupportForNetworks
import Sude.FWFourFamilyRoleCoverage

/-! Transfer the selected growth diagonal contributions to a supplied CY
completion of the same reference. Unreserved diagonals and off-diagonal pair
partners may change; no prime or later-flow assertion is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- A completion fixing the reference on the actual full reservation agrees
with the ordered square on its reserved diagonal cells. Hence all four signed
growth-diagonal identities and deviations transfer to that same completion. -/
theorem fw_growth_cy_diagonal_transfer {n : ℕ}
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (g : FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice f)
    (cy : Cell n ≃ Fin (n*n))
    (hcy : ∀ z ∈ fwThetaFamilyFull f, entry cy z = entry oldReference z) :
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    let μ := fun j => (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6 * (n + 8) : ℕ)
    (∀ z ∈ fwThetaFamilyFull f, z ∈ mainCells n ∨ z ∈ antiCells n → entry cy z = entry f.ordered z) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry cy z : ℝ)) =
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry cy z : ℝ)) =
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry cy z : ℝ)) =
      (∑ j, ∑ q ∈ g.T j, growthStageMidpoint (f.stages.get j) q) - 6 * ∑ j, ((f.stages.get j).gap : ℝ) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry cy z : ℝ)) =
      (∑ j, ∑ q ∈ g.U j, growthStageMidpoint (f.stages.get j) q) - 6 * ∑ j, ((f.stages.get j).gap : ℝ) ∧
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry cy z : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤ ((poolMaximum n : ℝ) / 6) / 2 ∧
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry cy z : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤
        ((n + 8 : ℝ) / (2 * (n + 6))) * ((poolMaximum n : ℝ) / 6) := by
  classical
  dsimp only
  let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
    f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  dsimp only at hgeom
  have hsub : roles ⊆ fwThetaFamilyFull f := by
    rw [net.roles_eq]
    simpa only [fwThetaFamilyFull] using hgeom.2.2.1
  have hgrowth : Finset.univ.image growth ⊆ fwThetaFamilyFull f := by
    intro z hz
    apply hsub
    rw [net.roles_eq]
    apply Finset.mem_union_right
    have heq := bt_growing_offset_pair_cells_image (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    change z ∈ Finset.univ.image growth at hz
    rw [heq] at hz
    exact hz
  have hpoint : ∀ z ∈ fwThetaFamilyFull f, z ∈ mainCells n ∨ z ∈ antiCells n →
      entry cy z = entry f.ordered z := by
    intro z hz hd
    have hrect : z ∈ packedRectangleSupport f.hs choice := by
      dsimp only [fwThetaFamilyFull] at hz
      rcases Finset.mem_union.mp hz with h | hcol
      · rcases Finset.mem_union.mp h with hrect | hrow
        · exact hrect
        · have hoff := f.hrows.support_off_diagonals z hrow
          exact (hd.elim hoff.1 hoff.2).elim
      · have hoff := (f.hcols.transposed_support_safe z hcol).2
        exact (hd.elim hoff.1 hoff.2).elim
    exact (hcy z hz).trans (net.rectangle_fixed z hrect)
  have hmain : (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry cy z : ℝ)) =
      ∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry f.ordered z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact_mod_cast hpoint z (hgrowth hz'.1) (Or.inl hz'.2)
  have hanti : (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry cy z : ℝ)) =
      ∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry f.ordered z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact_mod_cast hpoint z (hgrowth hz'.1) (Or.inr hz'.2)
  refine ⟨hpoint, hmain, hanti, ?_, ?_, ?_, ?_⟩
  · rw [hmain]
    exact g.main_identity
  · rw [hanti]
    exact g.anti_identity
  · rw [hmain]
    exact g.main_deviation
  · rw [hanti]
    exact g.anti_deviation

end
end Sude
