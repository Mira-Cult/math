import Sude.FWSelectedCapacitySeedChainCYTargets
import Sude.FWSelectedCapacityReachablePrime
import Sude.TargetMeanReachable
import Sude.PackedLabelRectangleSupport
import Sude.FWT75NominalSeedChainTargets

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
local notation "Y[" n "]" => ((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
local notation "D[" n "]" => (Y[n] / 1240)

/-- Conditional same-witness CY repair when both forward intervals cover the
upper half of the target window; mean averaging supplies one target index. -/
theorem fw_selected_capacity_mean_window_cy_prime {β : Type*} [DecidableEq β]
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n m h : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hn : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseedPool : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hseedCount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (hm : 2 ≤ m) (hh : h ∈ t75FavorableGaps)
    (narrow wide : Finset β) (low gap : β → ℕ)
    (hdis : Disjoint narrow wide) (hcount : 2*narrow.card+5 ≤ wide.card)
    (hlen : m + (narrow ∪ wide).card = n)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        Y[n]-D[n] ≤ (p : ℝ) ∧ (p : ℝ) ≤ Y[n] ∧ Y[n] ≤ (q : ℝ) ∧ (q : ℝ) ≤ Y[n]+D[n])
    (hprime : ∀ i ∈ narrow ∪ wide, Nat.Prime (low i) ∧ Nat.Prime (low i+gap i))
    (hwindow : ∀ i ∈ narrow ∪ wide, Y[n]-D[n] ≤ (low i : ℝ) ∧ ((low i+gap i : ℕ) : ℝ) ≤ Y[n]+D[n])
    (seed : Finset β) (labels : List β)
    (hS : seed ∪ labels.toFinset = narrow ∪ wide)
    (hseed : ∀ i ∈ seed, gap i = h)
    (hnodup : labels.Nodup) (hfresh : ∀ i ∈ labels, i ∉ seed)
    (hchain : StepGapChain gap h (∑ i ∈ seed, gap i) labels)
    (hnarrow : ∀ i ∈ narrow, |(low i : ℝ) + (gap i : ℝ)/2 - Y[n]| ≤ D[n]/2)
    (hwide : ∀ i ∈ wide, |(low i : ℝ) + (gap i : ℝ)/2 - Y[n]| ≤ D[n]/4)
    (hgap : ∀ i ∈ wide, D[n] ≤ (gap i : ℝ)) :
    ∃ (xs : List {r : ℕ // r < h ∧ Nat.Coprime r h})
      (lo hi : {r : ℕ // r < h ∧ Nat.Coprime r h} → ℕ)
      (values : List ℕ) (chosen : Finset β),
      xs.length = m ∧ chosen ⊆ narrow ∪ wide ∧
      List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values ∧
      let targets := values ++ (narrow ∪ wide).toList.map (fun i => if i ∈ chosen then low i+gap i else low i)
      ∃ ht : targets.length = n, ∃ primeTargets : Fin n → ℕ,
        (∀ i, primeTargets i = targets.get ((finCongr ht.symm) i)) ∧
        (∑ i, primeTargets i) = Lucas.poolTotal n ∧
        (∀ i, Nat.Prime (primeTargets i) ∧ Odd (primeTargets i) ∧ |(primeTargets i : ℝ)-Y[n]| ≤ D[n]) ∧
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
        (mainSum cy : ℝ) ≤ Y[n] → (antiSum cy : ℝ) ≤ Y[n] →
        Y[n] + D[n] ≤ (mainSum cy : ℝ) + 2 * (evenGridCenter f.last : ℝ) →
        Y[n] + D[n] ≤ (antiSum cy : ℝ) + 2 * (evenGridCenter f.last : ℝ) →
        ∃ (i : Fin n) (result : Cell n ≃ Fin (n*n)),
          (∀ r, rowSum result r = rowSum out r) ∧
          (∀ c, columnSum result c = columnSum out c) ∧
          mainSum result = primeTargets i ∧ antiSum result = primeTargets i ∧ Valid result ∧
          Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
          (∀ z ∈ keep, entry result z = entry out z))
    ) := by
  classical
  obtain ⟨xs, lo, hi, values, chosen, hxs, hchosen, hchoices, ht, target, hget, hsum, hcert,
    hgrids, out, hrow, hcol, hmain, hanti, hrect, hpool, hinj, hoff, himage, hdiag, hfull, hunused, hrepair⟩ :=
    fw_selected_capacity_seed_chain_cy_reachable_prime mv bmor lower upper sharp upperSharp hnlo hnhi hn
      otherChoice a seeds hseedPool hseedPrime hseedCount hm hh narrow wide low gap hdis hcount hlen
      hsupply hprime hwindow seed labels hS hseed hnodup hfresh hchain hnarrow hwide hgap
  refine ⟨xs, lo, hi, values, chosen, hxs, hchosen, hchoices, ht, target, hget, hsum, hcert,
    hgrids, out, hrow, hcol, hmain, hanti, hrect, hpool, hinj, hoff, himage, hdiag, hfull, hunused, ?_⟩
  dsimp only at hrepair ⊢
  intro keep hprotect hml hal hmu hau
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseedPool hseedPrime hseedCount
  let f := w.family
  let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hn otherChoice a seeds hseedPool hseedPrime hseedCount
  let completion := old.2.2.2.2.2.2
  let cy := Classical.choose (Classical.choose_spec completion)
  have hnpos : 0 < n := by omega
  have htotal : (Lucas.poolTotal n : ℝ) = (n : ℝ) * Y[n] := by
    have h := t75_pool_mean_line_total hnpos
    rw [t75_line_mean_eq_order_mul_pool_mean hnpos] at h
    rw [prescribedPoolValues_mean]
    nlinarith
  have hmean : (∑ i, (target i : ℝ)) = (n : ℝ) * Y[n] := by
    rw [← Nat.cast_sum, hsum, htotal]
  have hupper : ∀ i, (target i : ℝ) ≤ Y[n] + D[n] := by
    intro i
    have hh := (abs_le.mp (hcert i).2.2).2
    linarith
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := target_mean_forward_reachable hnpos target Y[n] D[n]
    (mainSum cy) (antiSum cy) (evenGridCenter f.last) hmean hupper hml hal hmu hau
  obtain ⟨result, hr, hc, hm', ha', hv, hp, hi, hk⟩ := hrepair keep i hprotect hi1 hi2 hi3 hi4
  exact ⟨i, result, hr, hc, hm', ha', hv, hp, hi, hk⟩
end
end Sude
