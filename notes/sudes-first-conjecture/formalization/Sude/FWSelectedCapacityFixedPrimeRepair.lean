import Sude.FWSelectedCapacityNominalCYTargets
import Sude.T75FixedPrimeInsertion
import Sude.FWT75NominalThetaDomain
import Sude.T75PoolParity
import Sude.PackedReachablePrimeDiagonal
import Sude.PackedLabelRectangleSupport
/-! Conditional fixed-prime target insertion and physical repair on one
capacity-selected CY square. Prime supply and reachability remain explicit. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
local notation "Y[" n "]" => ((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
local notation "D[" n "]" => (Y[n] / 1240)

/-- Insert a supplied prime and route its exact target vector, then repair
both diagonals when that prime is reachable on the same selected CY square. -/
theorem fw_selected_capacity_fixed_prime_repair {β : Type*} [DecidableEq β]
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n m h : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hn : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseedPool : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hseedCount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (hm : 2 ≤ m) (hh : h ∈ t75FavorableGaps)
    (S : Finset β) (z : β) (low gap : β → ℕ)
    (hz : z ∉ S) (hzero : gap z = 0) (hqprime : Nat.Prime (low z))
    (hlen : m + S.card + 1 = n)
    (hq : |(low z : ℝ) - Y[n]| ≤ D[n]/4)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        Y[n]-D[n] ≤ (p : ℝ) ∧ (p : ℝ) ≤ Y[n] ∧ Y[n] ≤ (q : ℝ) ∧ (q : ℝ) ≤ Y[n]+D[n])
    (hcontrolledPrime : ∀ i ∈ S, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i))
    (hwindow : ∀ i ∈ S, Y[n]-D[n] ≤ (low i : ℝ) ∧ ((low i+gap i : ℕ) : ℝ) ≤ Y[n]+D[n])
    (hgrid : CompleteStepGrid S gap h (∑ i ∈ S, gap i))
    (hmargin : |((∑ i ∈ S, low i : ℕ) : ℝ) + ((∑ i ∈ S, gap i : ℕ) : ℝ)/2 -
      (S.card : ℝ)*Y[n]| + D[n] + D[n]/4 ≤ ((∑ i ∈ S, gap i : ℕ) : ℝ)/2) :
    ∃ (xs : List {r : ℕ // r < h ∧ Nat.Coprime r h})
      (lo hi : {r : ℕ // r < h ∧ Nat.Coprime r h} → ℕ)
      (values : List ℕ) (chosen : Finset β),
      xs.length = m ∧ chosen ⊆ insert z S ∧
      List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values ∧
      let targets := values ++ (insert z S).toList.map (fun i => if i ∈ chosen then low i+gap i else low i)
      ∃ ht : targets.length = n, ∃ primeTargets : Fin n → ℕ,
        (∀ i, primeTargets i = targets.get ((finCongr ht.symm) i)) ∧
        (∑ i, primeTargets i) = Lucas.poolTotal n ∧
        (∀ i, Nat.Prime (primeTargets i) ∧ Odd (primeTargets i) ∧ |(primeTargets i : ℝ)-Y[n]| ≤ D[n]) ∧
        ∃ qidx, primeTargets qidx = low z ∧
    (
    let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseedPool hseedPrime hseedCount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let f := w.family
    let roles := w.roles
    let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseedPool hseedPrime hseedCount
    let completion := old.2.2.2.2.2.2
    let cy := Classical.choose (Classical.choose_spec completion)
    let full := fwThetaFamilyFull f
    fwRetainedProposition (fw_selected_capacity_cy_choice_grids mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseedPool hseedPrime hseedCount) ∧
    ∃ out : Cell n ≃ Fin (n*n),
      (∀ i, rowSum out i = primeTargets i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = primeTargets i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum cy ∧ antiSum out = antiSum cy ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ roles, entry out z = entry cy z) ∧
      roles.image (entry out) = roles.image (entry cy) ∧
      (∀ z ∈ unreservedDiagonalCells full, entry out z = entry cy z) ∧
      full.image (entry out) = full.image (entry cy) ∧
      actualUnusedPool out full = actualUnusedPool cy full ∧
      (∀ (keep : Finset (Cell n)),
        let active := fwActiveRectangleLabels n f.stages.length f.stageCap
        (∀ z ∈ keep, ∀ j ∈ active,
          z ∉ rectangleCells (RectanglePacking.firstRow f.hs j) (RectanglePacking.secondRow f.hs j)
            (RectanglePacking.firstColumn f.hs choice j) (RectanglePacking.secondColumn f.hs choice j)) →
        0 ≤ (low z : ℤ) - (mainSum cy : ℤ) →
        (low z : ℤ) - (mainSum cy : ℤ) ≤ 2 * evenGridCenter f.last →
        0 ≤ (low z : ℤ) - (antiSum cy : ℤ) →
        (low z : ℤ) - (antiSum cy : ℤ) ≤ 2 * evenGridCenter f.last →
        ∃ result : Cell n ≃ Fin (n*n),
          (∀ r, rowSum result r = rowSum out r) ∧
          (∀ c, columnSum result c = columnSum out c) ∧
          mainSum result = low z ∧ antiSum result = low z ∧ Valid result ∧
          Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
          (∀ z ∈ keep, entry result z = entry out z))
    ) := by
  classical
  have hnom := fw_t75_nominal_lower_above_finite_bmor bmor lower upper hnlo hnhi
  dsimp only at hnom
  have hD : 0 ≤ D[n] := by linarith
  have habove : (2 : ℝ) < Y[n] - D[n] := by linarith
  have hnpos : 0 < n := by omega
  have hcenter : (Lucas.poolTotal n : ℝ) = (n : ℝ) * Y[n] := by
    have hh := t75_pool_mean_line_total hnpos
    rw [t75_line_mean_eq_order_mul_pool_mean hnpos] at hh
    rw [prescribedPoolValues_mean]
    nlinarith
  obtain ⟨xs, lo, hi, values, chosen, hxs, hchosen, hchoices, ht, target, hget, hsum, hcert, i, hindex⟩ :=
    t75_fixed_prime_insertion hn hm hh S z low gap hz hzero hqprime hlen Y[n] D[n] hD hq
      hsupply hcontrolledPrime hwindow hgrid hcenter hmargin habove
  have hroute := fw_selected_capacity_nominal_cy_targets mv bmor upper lower sharp upperSharp
    n hnlo hnhi hn otherChoice a seeds hseedPool hseedPrime hseedCount target
    (fun i => (hcert i).1) (fun i => (hcert i).2.1) hsum (fun i => (hcert i).2.2)
  obtain ⟨hgrids, out, hrow, hcol, hmain, hanti, hrect, hpool, hinj, hoff, himage, hdiag, hfull, hunused⟩ := hroute
  refine ⟨xs, lo, hi, values, chosen, hxs, hchosen, hchoices, ht, target, hget, hsum, hcert, i, hindex,
    hgrids, out, hrow, hcol, hmain, hanti, hrect, hpool, hinj, hoff, himage, hdiag, hfull, hunused, ?_⟩
  dsimp only
  intro keep hprotect hml hmu hal hau
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseedPool hseedPrime hseedCount
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let f := w.family
  let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseedPool hseedPrime hseedCount
  let completion := old.2.2.2.2.2.2
  let cy := Classical.choose (Classical.choose_spec completion)
  let active := fwActiveRectangleLabels n f.stages.length f.stageCap
  let rgap := fwOrderedCanonicalRectangleGap f
  have hL : 3 ≤ fwJointRectangleCount n 254 := by have hh := f.hrect; omega
  have hmgrid : CompleteEvenGrid (active.filter fun i => choice i = true) rgap f.last := hgrids.2.2.2.2.1
  have hagrid : CompleteEvenGrid (active.filter fun i => choice i = false) rgap f.last := hgrids.2.2.2.2.2.1
  have hgaps : ∀ j ∈ active,
      entry cy (RectanglePacking.firstRow f.hs j, RectanglePacking.secondColumn f.hs choice j) =
        entry cy (RectanglePacking.firstRow f.hs j, RectanglePacking.firstColumn f.hs choice j) + rgap j ∧
      entry cy (RectanglePacking.secondRow f.hs j, RectanglePacking.firstColumn f.hs choice j) =
        entry cy (RectanglePacking.secondRow f.hs j, RectanglePacking.secondColumn f.hs choice j) + rgap j := by
    intro j hj
    simpa [cy, completion, old, choice, f, w, rgap, packedRectangleCorner] using hgrids.2.2.2.2.2.2.2 j hj
  have hagree : ∀ z ∈ packedLabelSupport f.hs choice active, entry out z = entry cy z := by
    intro z hz
    exact hrect z (packed_label_support_subset_rectangle_support f.hs choice active hz)
  have hr := packed_prime_diagonal_repair_reachable_target f.hs hL hn choice rgap active f.last f.last
    cy out keep hmgrid hagrid hgaps hprotect hagree hmain hanti
    (fun j => (hrow j).2) (fun j => (hcol j).2) target i (hcert i).1 (hcert i).2.1
    (by rw [hindex]; exact ⟨hml, hmu⟩) (by rw [hindex]; exact ⟨hal, hau⟩)
  obtain ⟨before, hbefore, hmgain, hagain, result, hrow', hcol', hmain', hanti', hvalid,
    hpool', hinj', hcenter', hkeep'⟩ := hr
  refine ⟨result, hrow', hcol', ?_, ?_, hvalid, hpool', hinj', hkeep'⟩
  · simpa [hindex] using hmain'
  · simpa [hindex] using hanti'
end
end Sude
