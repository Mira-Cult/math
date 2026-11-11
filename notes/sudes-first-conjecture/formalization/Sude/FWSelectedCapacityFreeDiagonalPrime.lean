import Sude.FWSelectedCapacityNominalCYTargets
import Sude.FWSelectedCapacityCYFamilyGrids
import Sude.PackedReachablePrimeDiagonal
import Sude.PackedLabelRectangleSupport

/-! Conditional same-CY repair to an independently supplied odd prime. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- The diagonal prime need not occur in the independently supplied row and
column vector. Its two exact same-CY reachability conditions remain explicit. -/
theorem fw_selected_capacity_free_diagonal_prime
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
    (q : ℕ) (hqprime : Nat.Prime q) (hqodd : Odd q) :
    let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let f := w.family
    let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseed hseedPrime hseedCount
    let completion := old.2.2.2.2.2.2
    let cy := Classical.choose (Classical.choose_spec completion)
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
        0 ≤ (q : ℤ) - (mainSum cy : ℤ) →
        (q : ℤ) - (mainSum cy : ℤ) ≤ 2 * evenGridCenter (fwCanonicalFamilyRadius f true) →
        0 ≤ (q : ℤ) - (antiSum cy : ℤ) →
        (q : ℤ) - (antiSum cy : ℤ) ≤ 2 * evenGridCenter (fwCanonicalFamilyRadius f false) →
        ∃ result : Cell n ≃ Fin (n*n),
          (∀ r, rowSum result r = target r) ∧ (∀ c, columnSum result c = target c) ∧
          mainSum result = q ∧ antiSum result = q ∧ Valid result ∧
          Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
          (∀ z ∈ keep, entry result z = entry out z) := by
  classical
  have hroute := fw_selected_capacity_nominal_cy_targets mv bmor upper lower sharp upperSharp
    n hnlo hnhi hn otherChoice a seeds hseed hseedPrime hseedCount target
    hprimeTarget hoddTarget htotal htarget
  obtain ⟨_, out, hrow, hcol, hmain, hanti, hrect, _⟩ := hroute
  have hfamily := fw_selected_capacity_cy_family_grids mv bmor upper lower sharp upperSharp n
    hnlo hnhi hn otherChoice a seeds hseed hseedPrime hseedCount
  refine ⟨out, hrow, hcol, hmain, hanti, hrect, ?_⟩
  dsimp only
  intro keep hprotect hml hmu hal hau
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let f := w.family
  let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseed hseedPrime hseedCount
  let completion := old.2.2.2.2.2.2
  let cy := Classical.choose (Classical.choose_spec completion)
  let active := fwActiveRectangleLabels n f.stages.length f.stageCap
  let rgap := fwOrderedCanonicalRectangleGap f
  have hL : 3 ≤ fwJointRectangleCount n 254 := by have hh := f.hrect; omega
  have hmgrid : CompleteEvenGrid (active.filter fun i => choice i = true) rgap (fwCanonicalFamilyRadius f true) := (hfamily.2.2.2.2.1 true).1
  have hagrid : CompleteEvenGrid (active.filter fun i => choice i = false) rgap (fwCanonicalFamilyRadius f false) := (hfamily.2.2.2.2.1 false).1
  have hgaps : ∀ j ∈ active,
      entry cy (RectanglePacking.firstRow f.hs j, RectanglePacking.secondColumn f.hs choice j) =
        entry cy (RectanglePacking.firstRow f.hs j, RectanglePacking.firstColumn f.hs choice j) + rgap j ∧
      entry cy (RectanglePacking.secondRow f.hs j, RectanglePacking.firstColumn f.hs choice j) =
        entry cy (RectanglePacking.secondRow f.hs j, RectanglePacking.secondColumn f.hs choice j) + rgap j := by
    intro j hj
    simpa [cy, completion, old, choice, f, w, rgap, packedRectangleCorner] using hfamily.2.2.2.2.2.1 j hj
  have hagree : ∀ z ∈ packedLabelSupport f.hs choice active, entry out z = entry cy z := by
    intro z hz
    exact hrect z (packed_label_support_subset_rectangle_support f.hs choice active hz)
  let i : Fin n := ⟨0, by omega⟩
  have hr := packed_prime_diagonal_repair_reachable_target f.hs hL hn choice rgap active
    (fwCanonicalFamilyRadius f true) (fwCanonicalFamilyRadius f false)
    cy out keep hmgrid hagrid hgaps hprotect hagree hmain hanti
    (fun j => (hrow j).2) (fun j => (hcol j).2) (fun _ => q) i hqprime hqodd
    ⟨hml, hmu⟩ ⟨hal, hau⟩
  obtain ⟨before, hbefore, hmgain, hagain, result, hrow', hcol', hmain', hanti', hvalid,
    hpool', hinj', hcenter', hkeep'⟩ := hr
  refine ⟨result, ?_, ?_, hmain', hanti', hvalid, hpool', hinj', hkeep'⟩
  · intro r; exact (hrow' r).trans (hrow r).1
  · intro c; exact (hcol' c).trans (hcol c).1
end
end Sude
