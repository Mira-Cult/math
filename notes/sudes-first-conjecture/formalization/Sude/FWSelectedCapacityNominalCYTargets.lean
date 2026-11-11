import Sude.FWSelectedCapacityCYChoiceGrid
import Sude.FWFirstBandCYRoutingBudget
import Sude.FWFirstBandTargetSpread
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- Route a supplied nominal prime vector through the selected grid-bearing CY square. -/
theorem fw_selected_capacity_nominal_cy_targets
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (target : Fin n → ℕ)
    (hprimeTarget : ∀ i, Nat.Prime (target i))
    (hoddTarget : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) :
    let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let f := w.family
    let roles := w.roles
    let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
    let completion := old.2.2.2.2.2.2
    let cy := Classical.choose (Classical.choose_spec completion)
    let full := fwThetaFamilyFull f
    fwRetainedProposition (fw_selected_capacity_cy_choice_grids mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount) ∧
    ∃ out : Cell n ≃ Fin (n*n),
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum cy ∧ antiSum out = antiSum cy ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ roles, entry out z = entry cy z) ∧
      roles.image (entry out) = roles.image (entry cy) ∧
      (∀ z ∈ unreservedDiagonalCells full, entry out z = entry cy z) ∧
      full.image (entry out) = full.image (entry cy) ∧
      actualUnusedPool out full = actualUnusedPool cy full := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  let f := w.family
  let p := w.p
  let roles := w.roles
  let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
  let completion := old.2.2.2.2.2.2
  let cy := Classical.choose (Classical.choose_spec completion)
  have facts := Classical.choose_spec (Classical.choose_spec completion)
  obtain ⟨hdiagfix, hfinalfix, hfullfix, hmainBound, hantiBound,
    hrowCY, hcolCY, hmainEq, hantiEq, hpoolCY, hinjCY, hrow, hcol, hflows⟩ := facts
  let P : (Cell n ≃ Fin (n*n)) → Prop := fun out =>
    (∀ z ∉ roles, entry out z = entry cy z) ∧
    roles.image (entry out) = roles.image (entry cy) ∧
    (∀ z ∈ unreservedDiagonalCells (fwThetaFamilyFull f), entry out z = entry cy z) ∧
    (fwThetaFamilyFull f).image (entry out) = (fwThetaFamilyFull f).image (entry cy) ∧
    actualUnusedPool out (fwThetaFamilyFull f) = actualUnusedPool cy (fwThetaFamilyFull f)
  have hrow' : ∀ i, |(rowSum cy i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n := by
    intro i
    exact le_of_lt (by simpa only [fwFrozenCYLineRadius] using hrow i)
  have hcol' : ∀ i, |(columnSum cy i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n := by
    intro i
    exact le_of_lt (by simpa only [fwFrozenCYLineRadius] using hcol i)
  have hspread : (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240 ≤
      10 * (poolMaximum n : ℝ) := le_of_lt (fw_first_band_target_spread_lt_ten bmor lower upper hnlo hnhi)
  have hbudget := le_of_lt (fw_first_band_cy_routing_budget_of_spread lower hnlo hnhi _ hspread)
  have hroute := fw_centered_prime_target_of_supplied_flows
    (N := (n/450)*poolMaximum n) hodd p cy (packedRectangleSupport f.hs choice) P target
    (fw_first_band_demand_rounding_threshold lower hnlo) hprimeTarget hoddTarget htotal htarget hrow' hcol' hbudget w.expansion
    (by
      intro fr hfr fc hfc
      obtain ⟨b, out, hr₀, hc₀, hm₀, ha₀, hrect₀, hoff₀, himage₀, hpool₀, hinj₀,
        hactive, hoff, hr, hc, hm, ha, hrect, himage, hpool, hinj, hdiag, hfull, hunused⟩ :=
        hflows fr hfr fc hfc
      exact ⟨out, hr, hc, hm, ha, hrect, hpool, hinj, hoff, himage, hdiag, hfull, hunused⟩)
  obtain ⟨out, hrowPrime, hcolPrime, hmainOut, hantiOut, hrectOut, hpoolOut, hinjOut, hP⟩ := hroute
  refine ⟨fw_selected_capacity_cy_choice_grids mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount, ?_⟩
  exact ⟨out, hrowPrime, hcolPrime, hmainOut, hantiOut, hrectOut, hpoolOut, hinjOut,
    hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2⟩
end
end Sude
