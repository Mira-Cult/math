import Sude.FWProjectedCYSpareTargetRouting
import Sude.FWSelectedCapacityThetaWitness

/-! Instantiate the projected spare-rebalancing route on one selected capacity
witness. The target vector remains supplied; this does not identify another CY
completion or supply a common diagonal prime. -/

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- For the actual selected family and network, construct one CY candidate,
rebalance its spare cells, and route supplied nominal odd-prime targets on the
resulting square. All output equalities concern these exact chosen objects. -/
theorem fw_selected_capacity_cy_spare_nominal_target_routing
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hseedCount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) :
    let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
    let f := w.family
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let full := fwThetaFamilyFull f
    let spare := packedRectangleSupport f.hs choice \ activeRectangleSupport f.hs choice
      (fwActiveRectangleLabels n f.stages.length f.stageCap)
    ∃ (cy : Cell n ≃ Fin (n*n)) (σ : Equiv.Perm (Cell n)) (out : Cell n ≃ Fin (n*n)),
      (∀ z ∈ full, entry cy z = entry w.oldReference z) ∧
      (∀ z ∉ spare, σ z = z) ∧
      (∀ z ∈ w.roles, σ z = z) ∧
      (∀ z ∈ activeRectangleSupport f.hs choice (fwActiveRectangleLabels n f.stages.length f.stageCap), σ z = z) ∧
      |(∑ z ∈ spare ∩ mainCells n, (entry (σ.trans cy) z : ℝ)) -
        (∑ z ∈ spare ∩ antiCells n, (entry (σ.trans cy) z : ℝ))| ≤ (poolMaximum n : ℝ) ∧
      (∀ r, |(rowSum (σ.trans cy) r : ℝ) - rowSum cy r| ≤ (poolMaximum n : ℝ)) ∧
      (∀ c, |(columnSum (σ.trans cy) c : ℝ) - columnSum cy c| ≤ (poolMaximum n : ℝ)) ∧
      full.image (entry (σ.trans cy)) = full.image (entry cy) ∧
      actualUnusedPool (σ.trans cy) full = actualUnusedPool cy full ∧
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum (σ.trans cy) ∧ antiSum out = antiSum (σ.trans cy) ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry (σ.trans cy) z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ w.roles, entry out z = entry (σ.trans cy) z) ∧
      w.roles.image (entry out) = w.roles.image (entry (σ.trans cy)) ∧
      full.image (entry out) = full.image (entry cy) ∧
      actualUnusedPool out full = actualUnusedPool cy full := by
  classical
  dsimp only
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
  exact fw_projected_cy_spare_nominal_target_routing bmor lower upper hnlo hnhi hodd otherChoice
    w.family w.p w.oldReference w.roles w.network w.expansion target hprime htodd htotal htarget

end
end Sude
