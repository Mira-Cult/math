import Sude.FWSelectedSpareRebalance
import Sude.OffSupportReservationImage

/-! Rebalance the actual spare cells of a supplied CY candidate while keeping
its role cells fixed and preserving its reservation value image. This does not
construct a CY square, transport flows, or supply any prime. -/

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- A supplied reservation decomposition permits the actual spare-pair
permutation to be used on the supplied square. The transformed square is a new
square; no equality with an independently selected completion is asserted. -/
theorem fw_supplied_cy_spare_rebalance {n P : ℕ}
    (hnlo : 19485 ≤ n) (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (full roles : Finset (Cell n)) (cy : Cell n ≃ Fin (n*n))
    (hspare : full \ roles = packedRectangleSupport hs (fwSelectedThetaChoice hnlo otherChoice) \
      activeRectangleSupport hs (fwSelectedThetaChoice hnlo otherChoice) (fwActiveRectangleLabels n P hP)) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    ∃ σ : Equiv.Perm (Cell n),
      (∀ z ∉ spare, σ z = z) ∧
      (∀ z ∈ roles, σ z = z) ∧
      (∀ z ∉ full, σ z = z) ∧
      (∀ z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP), σ z = z) ∧
      |(∑ z ∈ spare ∩ mainCells n, (entry (σ.trans cy) z : ℝ)) -
        (∑ z ∈ spare ∩ antiCells n, (entry (σ.trans cy) z : ℝ))| ≤ (poolMaximum n : ℝ) ∧
      (∀ r, |(rowSum (σ.trans cy) r : ℝ) - rowSum cy r| ≤ (poolMaximum n : ℝ)) ∧
      (∀ c, |(columnSum (σ.trans cy) c : ℝ) - columnSum cy c| ≤ (poolMaximum n : ℝ)) ∧
      full.image (entry (σ.trans cy)) = full.image (entry cy) ∧
      actualUnusedPool (σ.trans cy) full = actualUnusedPool cy full := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  have hs' : full \ roles = spare := hspare
  obtain ⟨σ, hoff, hdiag, hrow, hcol⟩ := fw_selected_spare_rebalance hnlo hP hs otherChoice cy
  have hsub : spare ⊆ full := by
    intro z hz
    have hz' : z ∈ full \ roles := by simpa only [hs'] using hz
    exact (Finset.mem_sdiff.mp hz').1
  have hroles : ∀ z ∈ roles, σ z = z := by
    intro z hz
    apply hoff z
    intro hzs
    have hz' : z ∈ full \ roles := by simpa only [hs'] using hzs
    exact (Finset.mem_sdiff.mp hz').2 hz
  have hfull : ∀ z ∉ full, σ z = z := by
    intro z hz
    apply hoff z
    exact fun hzs => hz (hsub hzs)
  have hactive : ∀ z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP), σ z = z := by
    intro z hz
    apply hoff z
    intro hzs
    exact (Finset.mem_sdiff.mp hzs).2 hz
  have himages := off_support_reservation_value_images full spare hsub σ hoff cy
  exact ⟨σ, hoff, hroles, hfull, hactive, hdiag, hrow, hcol, himages.1, himages.2.2⟩

end
end Sude
