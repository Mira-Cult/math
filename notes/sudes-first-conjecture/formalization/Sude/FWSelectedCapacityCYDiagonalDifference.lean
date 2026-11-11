import Sude.FWSelectedCapacityFrozenCYAllLineFlows
import Sude.EqualCardCenteredBaseline
import Sude.CentralDiagonalGeometry

/-! The selected CY diagonal difference has a single centered reserved
baseline and the two completion errors. No balance, overlap or prime assertion
is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- On the exact capacity-selected CY witness, the full-reservation baseline
is centered at the actual unused mean of the same selected reference. -/
theorem fw_selected_capacity_cy_diagonal_difference
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
    let f := w.family
    let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
    let completion := old.2.2.2.2.2.2
    let cy := Classical.choose (Classical.choose_spec completion)
    let full := fwThetaFamilyFull f
    let ν := centralEntriesMean (actualUnusedPool w.oldReference full) centralPoolValue
    let reservedDiff := (∑ z ∈ mainCells n ∩ full, ((entry w.oldReference z : ℝ) - ν)) -
      (∑ z ∈ antiCells n ∩ full, ((entry w.oldReference z : ℝ) - ν))
    |(mainSum cy : ℝ) - (antiSum cy : ℝ)| ≤ |reservedDiff| + (5/2 : ℝ) * poolMaximum n := by
  classical
  dsimp only
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
  let completion := old.2.2.2.2.2.2
  let facts := Classical.choose_spec (Classical.choose_spec completion)
  have hcard : (mainCells n).card = (antiCells n).card := by simp [mainCells_card, antiCells_card]
  have hmain := facts.2.2.2.1
  have hanti := facts.2.2.2.2.1
  -- Invoke the finite baseline identity and the two same-witness errors.
  have h := equal_card_centered_baseline_error (mainCells n) (antiCells n)
    (fwThetaFamilyFull w.family) (fun z => (entry w.oldReference z : ℝ))
    (centralEntriesMean (actualUnusedPool w.oldReference (fwThetaFamilyFull w.family)) centralPoolValue)
    (mainSum (Classical.choose (Classical.choose_spec completion)) : ℝ)
    (antiSum (Classical.choose (Classical.choose_spec completion)) : ℝ)
    (poolMaximum n : ℝ) ((3/2 : ℝ)*poolMaximum n) hcard hmain hanti
  convert h using 1 <;> ring

end
end Sude
