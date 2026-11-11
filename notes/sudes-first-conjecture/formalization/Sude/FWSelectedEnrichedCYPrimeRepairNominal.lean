import Sude.FWSelectedEnrichedCYPrimeRepairBudget
import Sude.FWFirstBandTargetSpread

/-! The nominal first-band target window pays the selected repair's routing
budget. Prime targets, endpoint windows and the conditional physical repair
premises are still supplied. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Use the source's nominal target spread `nμ/1240` on one selected enriched
witness. All target-vector and nested diagonal-repair premises of the original
theorem are retained; no target existence or unconditional diagonal primality
is inferred. -/
theorem fw_selected_enriched_theta_cy_prime_diagonal_repair_of_nominal_spread
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (target : Fin n → ℕ) (D : ℝ)
    (hprime : ∀ i, Nat.Prime (target i)) (htargetOdd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ D)
    (hnominal : D = (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) :
    let w := fwSelectedEnrichedThetaWitness mv bmor upper lower sharp upperSharp
      n hnlo hnhi otherChoice a seeds hseed hseedPrime hcount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let f := w.family
    let p := w.p
    let oldReference := w.oldReference
    let roles := w.roles
    let g := w.diagonal
    (∀ i v, p i v ≠ v) ∧
    (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
    Nonempty (FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice f) ∧
    Nonempty (FWThetaRoleValueInputs f seeds) ∧
    (
    let full := fwThetaFamilyFull f
    let final := full ∪ unreservedDiagonalCells full
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    let μ := fun j => (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6 * (n + 8) : ℕ)
    ∃ diag cy out : Cell n ≃ Fin (n*n),
    (
      (∀ z ∈ full, entry diag z = entry oldReference z) ∧
      (∀ z ∈ final, entry cy z = entry diag z) ∧
      (∀ z ∈ full, entry cy z = entry oldReference z) ∧
      |(mainSum cy : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry oldReference z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum cy : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry oldReference z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      mainSum cy = mainSum diag ∧ antiSum cy = antiSum diag ∧
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum cy ∧ antiSum out = antiSum cy ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ roles, entry out z = entry cy z) ∧
      roles.image (entry out) = roles.image (entry cy) ∧
      (∀ z ∈ unreservedDiagonalCells full, entry out z = entry cy z) ∧
      full.image (entry out) = full.image (entry cy) ∧
      actualUnusedPool out full = actualUnusedPool cy full ∧
    (∀ z ∈ fwThetaFamilyFull f, z ∈ mainCells n ∨ z ∈ antiCells n → entry out z = entry f.ordered z) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) =
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) =
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) =
      (∑ j, ∑ q ∈ g.T j, growthStageMidpoint (f.stages.get j) q) - 6 * ∑ j, ((f.stages.get j).gap : ℝ) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) =
      (∑ j, ∑ q ∈ g.U j, growthStageMidpoint (f.stages.get j) q) - 6 * ∑ j, ((f.stages.get j).gap : ℝ) ∧
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤ ((poolMaximum n : ℝ) / 6) / 2 ∧
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤
        ((n + 8 : ℝ) / (2 * (n + 6))) * ((poolMaximum n : ℝ) / 6)
    ) ∧
    (∀ (gap : Fin (fwJointRectangleCount n 254) → ℕ)
      (labels : Finset (Fin (fwJointRectangleCount n 254))) (Rm Ra : ℕ)
      (keep : Finset (Cell n)) (Udiag : ℝ),
      CompleteEvenGrid (labels.filter fun i => choice i = true) gap Rm →
      CompleteEvenGrid (labels.filter fun i => choice i = false) gap Ra →
      (∀ i ∈ labels,
        entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
          entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) + gap i ∧
        entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
          entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) + gap i) →
      (∀ z ∈ keep, ∀ i ∈ labels,
        z ∉ rectangleCells (RectanglePacking.firstRow f.hs i) (RectanglePacking.secondRow f.hs i)
          (RectanglePacking.firstColumn f.hs choice i) (RectanglePacking.secondColumn f.hs choice i)) →
      ∃ before : Finset (Fin (fwJointRectangleCount n 254)), before ⊆ labels ∧
        let reference := packedTradeSequence f.hs choice cy before.toList
        (mainSum reference : ℤ) - (mainSum cy : ℤ) = evenGridCenter Rm ∧
        (antiSum reference : ℤ) - (antiSum cy : ℤ) = evenGridCenter Ra ∧
        (|(mainSum reference : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ Udiag →
         |(antiSum reference : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ Udiag →
         Udiag + D ≤ (evenGridCenter Rm : ℝ) →
         Udiag + D ≤ (evenGridCenter Ra : ℝ) →
         ∃ (q : ℕ) (result : Cell n ≃ Fin (n*n)),
           Nat.Prime q ∧ (∃ i, q = target i) ∧
           (∀ r, rowSum result r = rowSum out r) ∧
           (∀ c, columnSum result c = columnSum out c) ∧
           mainSum result = q ∧ antiSum result = q ∧ Valid result ∧
           Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
           (∀ z ∈ keep, entry result z = entry out z))) ) := by
  have hspread : D ≤ 10 * (poolMaximum n : ℝ) := by
    rw [hnominal]
    exact le_of_lt (fw_first_band_target_spread_lt_ten bmor lower upper hnlo hnhi)
  exact fw_selected_enriched_theta_cy_prime_diagonal_repair_of_spread mv bmor upper lower sharp upperSharp
    n hnlo hnhi hodd otherChoice a seeds hseed hseedPrime hcount target D hprime htargetOdd htotal htarget hspread

end
end Sude
