import Sude.FWThetaFamilyWitness
import Sude.FWFirstBandSeedRadiusBound

/-! Subtract two seed invoices on the same supplied family.  The incidence
equalities are explicit inputs; this alone asserts no physical support or
completed-square conclusion. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem fw_seed_signed_diagonal_of_equal_invoices {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice)
    (hweight : ∀ j : Fin 16,
      (∑ q : Fin (6*(n+8)), physicalPairLineWeight
        (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc)
        (fun c => c ∈ mainCells n) (j,q)) =
      (∑ q : Fin (6*(n+8)), physicalPairLineWeight
        (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc)
        (fun c => c ∈ antiCells n) (j,q)))
    (horient :
      (∑ p : Fin 16 × Fin (6*(n+8)), physicalPairLineOrientation
        (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc)
        (fun c => c ∈ mainCells n) p) =
      (∑ p : Fin 16 × Fin (6*(n+8)), physicalPairLineOrientation
        (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc)
        (fun c => c ∈ antiCells n) p)) :
    let seed := fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc
    |(∑ z ∈ (Finset.univ.image seed).filter (fun z => z ∈ mainCells n), (entry f.ordered z : ℝ)) -
     (∑ z ∈ (Finset.univ.image seed).filter (fun z => z ∈ antiCells n), (entry f.ordered z : ℝ))| ≤
      2 * Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2) := by
  classical
  let lm : Fin ((n+n)+2) := finSumFinEquiv (Sum.inr (0 : Fin 2))
  let la : Fin ((n+n)+2) := finSumFinEquiv (Sum.inr (1 : Fin 2))
  have hm := f.hseedScore lm
  have ha := f.hseedScore la
  simp only [lm, physicalAllLineCells, Equiv.symm_apply_apply, if_true] at hm
  simp only [la, physicalAllLineCells, Equiv.symm_apply_apply, show (1 : Fin 2) ≠ 0 by decide, if_false] at ha
  simp only [show ((2 : ℝ) / 2) = 1 by norm_num, mul_one] at hm ha
  have hw : (∑ j : Fin 16, ((∑ i, physicalPairLineWeight
      (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc)
      (fun c => c ∈ mainCells n) (j,i)) *
      ((∑ i, (((entry f.grown (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc ((j,i),false)) : ℝ) +
        entry f.grown (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc ((j,i),true))) / 2)) / ((6*(n+8) : ℕ) : ℝ)))) =
    (∑ j : Fin 16, ((∑ i, physicalPairLineWeight
      (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc)
      (fun c => c ∈ antiCells n) (j,i)) *
      ((∑ i, (((entry f.grown (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc ((j,i),false)) : ℝ) +
        entry f.grown (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc ((j,i),true))) / 2)) / ((6*(n+8) : ℕ) : ℝ)))) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hweight j]
  rw [hw, horient] at hm
  dsimp only at hm ha ⊢
  rw [abs_le] at hm ha ⊢
  constructor <;> linarith

theorem fw_first_band_twice_seed_radius_le_three_pool
    (lower : RSIndexLower) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    2 * Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2) ≤
      3 * (poolMaximum n : ℝ) := by
  have h := fw_first_band_seed_radius_le_three_halves lower hnlo hnhi
  linarith

end
end Sude
