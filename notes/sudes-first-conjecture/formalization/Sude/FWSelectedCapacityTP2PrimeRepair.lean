import Sude.FWSelectedCapacityFreeDiagonalPrime
import Sude.FWT75NominalThetaDomain
import Sude.APInterval
/-! Conditional prime extraction from a supplied modulus-two interval count
on the exact selected CY overlap. No analytic count or overlap is inferred. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- Use a supplied TP2-shaped interval count to repair the same selected CY
square when the stated interval lies in both physical reachable ranges. -/
theorem fw_selected_capacity_tp2_prime_repair
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hn : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hseedCount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (target : Fin n → ℕ) (hprimeTarget : ∀ i, Nat.Prime (target i))
    (hoddTarget : ∀ i, Odd (target i)) (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240)
    (b c : ℝ) (_hb : 2 < b) (hbc : b < c)
    (hnominal : (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue -
        ((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) ≤ b ∧
      c ≤ (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue +
        ((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240))
    (_hwidth : ((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) / 2 ≤ c-b)
    (hcount : (c-b) / (2 * Real.log (2 * ((n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue))) ≤ ((apInterval b c 2 1).card : ℝ))
    (hcontain :
      let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
      let f := w.family
      let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseed hseedPrime hseedCount
      let completion := old.2.2.2.2.2.2
      let cy := Classical.choose (Classical.choose_spec completion)
      (mainSum cy : ℝ) ≤ b ∧
      c ≤ (mainSum cy : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℝ) ∧
      (antiSum cy : ℝ) ≤ b ∧
      c ≤ (antiSum cy : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℝ)) :
    let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let f := w.family
    let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseed hseedPrime hseedCount
    let completion := old.2.2.2.2.2.2
    let cy := Classical.choose (Classical.choose_spec completion)
    ∃ q : ℕ, Nat.Prime q ∧ Odd q ∧ b < (q : ℝ) ∧ (q : ℝ) ≤ c ∧
    ∃ out : Cell n ≃ Fin (n*n),
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum cy ∧ antiSum out = antiSum cy ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) ∧
      ∀ keep : Finset (Cell n),
        let active := fwActiveRectangleLabels n f.stages.length f.stageCap
        (∀ z ∈ keep, ∀ j ∈ active,
          z ∉ rectangleCells (RectanglePacking.firstRow f.hs j) (RectanglePacking.secondRow f.hs j)
            (RectanglePacking.firstColumn f.hs choice j) (RectanglePacking.secondColumn f.hs choice j)) →
        ∃ result : Cell n ≃ Fin (n*n),
          (∀ r, rowSum result r = target r) ∧ (∀ c, columnSum result c = target c) ∧
          mainSum result = q ∧ antiSum result = q ∧ Valid result ∧
          Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
          (∀ z ∈ keep, entry result z = entry out z) := by
  classical
  let Y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have hnom := fw_t75_nominal_lower_above_finite_bmor bmor lower upper hnlo hnhi
  dsimp only at hnom
  have hY : 1 < 2 * Y := by dsimp [Y]; linarith
  have hlog : 0 < Real.log (2*Y) := Real.log_pos hY
  have hquot : 0 < (c-b) / (2*Real.log (2*Y)) := by positivity
  have hcount' : 0 < ((apInterval b c 2 1).card : ℝ) := lt_of_lt_of_le hquot hcount
  have hne : (apInterval b c 2 1).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hcount'
  obtain ⟨q, hqmem⟩ := hne
  have ⟨hqprime,hqlo,hqhi,hqmod⟩ := (mem_apInterval_iff b c 2 1 (by linarith) (by linarith) q).mp hqmem
  have hqne : q ≠ 2 := by
    intro heq
    subst q
    norm_num at hqlo
    linarith
  have hqodd : Odd q := Nat.odd_iff.mpr (hqprime.eq_two_or_odd.resolve_left hqne)
  have hroute := fw_selected_capacity_free_diagonal_prime mv bmor lower upper sharp upperSharp
    n hnlo hnhi hn otherChoice a seeds hseed hseedPrime hseedCount target hprimeTarget hoddTarget htotal htarget
    q hqprime hqodd
  obtain ⟨out, hrow, hcol, hmain, hanti, hrect, hrepair⟩ := hroute
  refine ⟨q, hqprime, hqodd, hqlo, hqhi, out, hrow, hcol, hmain, hanti, hrect, ?_⟩
  dsimp only at hcontain ⊢
  intro keep hprotect
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
  let f := w.family
  let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseed hseedPrime hseedCount
  let completion := old.2.2.2.2.2.2
  let cy := Classical.choose (Classical.choose_spec completion)
  have hmlo : (mainSum cy : ℝ) ≤ (q : ℝ) := hcontain.1.trans (le_of_lt hqlo)
  have hmhi : (q : ℝ) ≤ (mainSum cy : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℝ) := hqhi.trans hcontain.2.1
  have halo : (antiSum cy : ℝ) ≤ (q : ℝ) := hcontain.2.2.1.trans (le_of_lt hqlo)
  have hahi : (q : ℝ) ≤ (antiSum cy : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℝ) := hqhi.trans hcontain.2.2.2
  have hmlo' : (mainSum cy : ℤ) ≤ q := by exact_mod_cast hmlo
  have hmhi' : (q : ℤ) ≤ (mainSum cy : ℤ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℤ) := by exact_mod_cast hmhi
  have halo' : (antiSum cy : ℤ) ≤ q := by exact_mod_cast halo
  have hahi' : (q : ℤ) ≤ (antiSum cy : ℤ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℤ) := by exact_mod_cast hahi
  apply hrepair keep hprotect
  · change 0 ≤ (q : ℤ) - (mainSum cy : ℤ)
    omega
  · change (q : ℤ) - (mainSum cy : ℤ) ≤ 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℤ)
    omega
  · change 0 ≤ (q : ℤ) - (antiSum cy : ℤ)
    omega
  · change (q : ℤ) - (antiSum cy : ℤ) ≤ 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℤ)
    omega
end
end Sude
