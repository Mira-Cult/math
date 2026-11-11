import Sude.T75UnitBracketTargets
import Sude.T75TwoClassMidpointMargin
import Sude.FWThetaInputs
import Sude.ReservedPoolMean
namespace Sude
noncomputable section
set_option maxHeartbeats 2000000

private theorem scratch_t75_nominal_center {n : ℕ} (hn : 0 < n) :
    (Lucas.poolTotal n : ℝ) = (n : ℝ) * ((n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue) := by
  have h := t75_pool_mean_line_total hn
  rw [t75_line_mean_eq_order_mul_pool_mean hn] at h
  rw [prescribedPoolValues_mean]
  nlinarith

private theorem scratch_t75_nominal_window_positive
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let D : ℝ := y / 1240
    0 ≤ D ∧ (2 : ℝ) < y - D := by
  dsimp only
  rw [prescribedPoolValues_mean]
  have hn : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hXnat : 100 ≤ poolMaximum n := by
    have hp := fw_poolMaximum_gt_four_seed lower hnlo
    omega
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  have hm := (fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega)).1
  constructor <;> nlinarith

/-- Nominal T75 target vector from explicitly supplied bracket and controlled
    grid data on the same coordinate sets. Prime supply and grid existence
    remain hypotheses. -/
theorem fw_t75_nominal_two_class_targets {β : Type*} [DecidableEq β]
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n m h : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hn : Odd n)
    (hm : 2 ≤ m) (hh : h ∈ t75FavorableGaps)
    (narrow wide : Finset β) (low gap : β → ℕ)
    (hdis : Disjoint narrow wide) (hcount : 2*narrow.card+5 ≤ wide.card)
    (hlen : m + (narrow ∪ wide).card = n)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hDnominal : D = y / 1240)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y-D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y+D)
    (hprime : ∀ i ∈ narrow ∪ wide, Nat.Prime (low i) ∧ Nat.Prime (low i+gap i))
    (hwindow : ∀ i ∈ narrow ∪ wide, y-D ≤ (low i : ℝ) ∧ ((low i+gap i : ℕ) : ℝ) ≤ y+D)
    (hgrid : CompleteStepGrid (narrow ∪ wide) gap h (∑ i ∈ narrow ∪ wide, gap i))
    (hnarrow : ∀ i ∈ narrow, |(low i : ℝ) + (gap i : ℝ)/2 - y| ≤ D/2)
    (hwide : ∀ i ∈ wide, |(low i : ℝ) + (gap i : ℝ)/2 - y| ≤ D/4)
    (hgap : ∀ i ∈ wide, D ≤ (gap i : ℝ)) :
    ∃ (xs : List {r : ℕ // r < h ∧ Nat.Coprime r h})
      (lo hi : {r : ℕ // r < h ∧ Nat.Coprime r h} → ℕ)
      (values : List ℕ) (chosen : Finset β),
      xs.length = m ∧ chosen ⊆ narrow ∪ wide ∧
      List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values ∧
      let targets := values ++ (narrow ∪ wide).toList.map (fun i => if i ∈ chosen then low i+gap i else low i)
      ∃ ht : targets.length = n, ∃ f : Fin n → ℕ,
        (∀ i, f i = targets.get ((finCongr ht.symm) i)) ∧
        (∑ i, f i) = Lucas.poolTotal n ∧
        (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ)-y| ≤ D) := by
  have hnom : 0 ≤ D ∧ (2 : ℝ) < y-D := by
    rw [hDnominal, hy]
    exact scratch_t75_nominal_window_positive bmor lower upper hnlo hnhi
  have hcenter : (Lucas.poolTotal n : ℝ) = (n : ℝ)*y := by
    rw [hy]
    exact scratch_t75_nominal_center (by omega)
  have hmargin := t75_two_class_hmargin narrow wide low gap y D hnom.1 hdis hcount hnarrow hwide hgap
  exact t75_targets_from_unit_bracket_supply hn hm hh (narrow ∪ wide) low gap hlen y D hnom.1
    hsupply hprime hwindow hgrid hcenter hmargin hnom.2

end
end Sude
