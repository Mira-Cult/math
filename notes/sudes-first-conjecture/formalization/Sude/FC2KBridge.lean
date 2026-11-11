import Sude.DoublePairBatch
import Sude.APInterval
import Sude.EvenGrid

/-! Geometry and finite stock interfaces for FC2K's bridge stages. -/
namespace Sude
noncomputable section

/-- `min(R/X,1/2)*X`, written without a denominator. -/
def bridgeSpan (X R : ℝ) : ℝ := min R (X / 2)

def bridgeWidth (X R : ℝ) : ℝ := (3 / 100 : ℝ) * bridgeSpan X R
def bridgeLowStart (X R : ℝ) : ℝ := X / 2 - bridgeSpan X R / 2
def bridgeLowEnd (X R : ℝ) : ℝ := bridgeLowStart X R + bridgeWidth X R
def bridgeHighEnd (X R : ℝ) : ℝ := X / 2 + bridgeSpan X R / 2
def bridgeHighStart (X R : ℝ) : ℝ := bridgeHighEnd X R - bridgeWidth X R
def bridgeGapLower (X R : ℝ) : ℝ := bridgeSpan X R - 2 * bridgeWidth X R

/-- The denominator-free span is exactly the manuscript's rX. -/
theorem bridgeSpan_source (X R : ℝ) (hX : 0 < X) :
    bridgeSpan X R = min (R / X) (1 / 2) * X := by
  rw [min_mul_of_nonneg _ _ (le_of_lt hX), div_mul_cancel₀ R (ne_of_gt hX)]
  simp only [bridgeSpan]
  ring_nf

/-- FC2K3's increment, including the exact rational coefficient. -/
theorem bridgeGapLower_source (X R : ℝ) (hX : 0 < X) :
    bridgeGapLower X R =
      (1 - 2 * (3 / 100 : ℝ)) * (min (R / X) (1 / 2) * X) := by
  rw [← bridgeSpan_source X R hX]
  simp only [bridgeGapLower, bridgeWidth]
  ring

theorem bridgeSpan_properties (X R : ℝ) (hX : 0 < X) (hR : 0 < R) :
    0 < bridgeSpan X R ∧ bridgeSpan X R ≤ R ∧ bridgeSpan X R ≤ X / 2 := by
  exact ⟨lt_min hR (by linarith), min_le_left _ _, min_le_right _ _⟩

/-- Both half-open source windows have width H, are disjoint and lie in
[X/4,3X/4]; the guaranteed increment is strictly positive. -/
theorem bridge_window_geometry (X R : ℝ) (hX : 0 < X) (hR : 0 < R) :
    0 < bridgeWidth X R ∧ 0 < bridgeGapLower X R ∧
    X / 4 ≤ bridgeLowStart X R ∧
    bridgeLowStart X R < bridgeLowEnd X R ∧
    bridgeLowEnd X R < bridgeHighStart X R ∧
    bridgeHighStart X R < bridgeHighEnd X R ∧
    bridgeHighEnd X R ≤ 3 * X / 4 ∧
    bridgeLowEnd X R - bridgeLowStart X R = bridgeWidth X R ∧
    bridgeHighEnd X R - bridgeHighStart X R = bridgeWidth X R := by
  have hs := bridgeSpan_properties X R hX hR
  simp only [bridgeWidth, bridgeGapLower, bridgeLowStart, bridgeLowEnd,
    bridgeHighStart, bridgeHighEnd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [hs.1, hs.2.2]

/-- Every cross-pair from the exact checker-style windows has the source's
strict difference bounds; subtraction is proved safe before casting. -/
theorem bridge_cross_gap (X R : ℝ) (hX : 0 < X) (hR : 0 < R) (a b : ℕ)
    (ha : bridgeLowStart X R < (a : ℝ) ∧ (a : ℝ) ≤ bridgeLowEnd X R)
    (hb : bridgeHighStart X R < (b : ℝ) ∧ (b : ℝ) ≤ bridgeHighEnd X R) :
    a < b ∧ 0 < b - a ∧
      bridgeGapLower X R < ((b - a : ℕ) : ℝ) ∧
      ((b - a : ℕ) : ℝ) < bridgeSpan X R ∧
      ((b - a : ℕ) : ℝ) ≤ R := by
  have hg := bridge_window_geometry X R hX hR
  have hs := bridgeSpan_properties X R hX hR
  have habReal : (a : ℝ) < b := by linarith [hg.2.2.2.2.1]
  have hab : a < b := by exact_mod_cast habReal
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub (le_of_lt hab)
  refine ⟨hab, by omega, ?_, ?_, ?_⟩ <;>
    rw [hcast] <;>
    simp only [bridgeGapLower, bridgeWidth, bridgeLowStart, bridgeLowEnd,
      bridgeHighStart, bridgeHighEnd] at * <;> linarith [hs.2.1]

/-- Any ordered pair of prescribed entries has an even difference. -/
theorem pool_ordered_difference_even {n a b : ℕ} (ha : a ∈ pool n) (hb : b ∈ pool n)
    (hab : a ≤ b) : 2 ∣ b - a := by
  have haodd : Odd a := by
    obtain ⟨i, rfl⟩ := ha
    exact oddPrime_odd i.val
  have hbodd : Odd b := by
    obtain ⟨i, rfl⟩ := hb
    exact oddPrime_odd i.val
  obtain ⟨i, hi⟩ := haodd
  obtain ⟨j, hj⟩ := hbodd
  apply Nat.dvd_of_mod_eq_zero
  omega

/-- Exact FC2K bridge selection, conditional on the two actual side stocks
and their paid deletion budgets. Each selected block has a usable even gap. -/
theorem bridge_select_pool_blocks {n : ℕ} (X R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (low high removedLow removedHigh : Finset ℕ) (M k : ℕ)
    (hpoolLow : ∀ a ∈ low, a ∈ pool n) (hpoolHigh : ∀ b ∈ high, b ∈ pool n)
    (hlowWindow : ∀ a ∈ low,
      bridgeLowStart X R < (a : ℝ) ∧ (a : ℝ) ≤ bridgeLowEnd X R)
    (hhighWindow : ∀ b ∈ high,
      bridgeHighStart X R < (b : ℝ) ∧ (b : ℝ) ≤ bridgeHighEnd X R)
    (hlow : M + 2 * k + removedLow.card ≤ low.card)
    (hhigh : M + 2 * k + removedHigh.card ≤ high.card)
    (hgate : bridgeWidth X R + 1 < (M : ℝ) * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid (low \ removedLow) (high \ removedHigh)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, 2 ∣ b.high₁ - b.low₁ ∧
        bridgeGapLower X R < ((b.high₁ - b.low₁ : ℕ) : ℝ) ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) < bridgeSpan X R ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) ≤ R) := by
  have hgeom := bridge_window_geometry X R hX hR
  have horder : ∀ a ∈ low, ∀ b ∈ high, a < b := by
    intro a ha b hb
    exact (bridge_cross_gap X R hX hR a b (hlowWindow a ha) (hhighWindow b hb)).1
  have hspan : ∀ a ∈ low, ∀ b ∈ high,
      bridgeGapLower X R < ((b - a : ℕ) : ℝ) ∧
        ((b - a : ℕ) : ℝ) ≤ bridgeGapLower X R + 2 * bridgeWidth X R := by
    intro a ha b hb
    have h := bridge_cross_gap X R hX hR a b (hlowWindow a ha) (hhighWindow b hb)
    have heq : bridgeGapLower X R + 2 * bridgeWidth X R = bridgeSpan X R := by
      simp only [bridgeGapLower]
      ring
    exact ⟨h.2.2.1, by rw [heq]; exact le_of_lt h.2.2.2.1⟩
  obtain ⟨blocks, hlen, hvalid, hpair⟩ :=
    select_pool_double_pairs_fc2k low high removedLow removedHigh M k
      (bridgeGapLower X R) (bridgeWidth X R) hpoolLow hpoolHigh horder hspan
      hlow hhigh (le_of_lt hgeom.1) hgate
  refine ⟨blocks, hlen, hvalid, hpair, ?_⟩
  intro b hb
  have hv := hvalid b hb
  have hl := (Finset.mem_sdiff.mp hv.1).1
  have hh := (Finset.mem_sdiff.mp hv.2.2.1).1
  have hg := bridge_cross_gap X R hX hR b.low₁ b.high₁ (hlowWindow _ hl) (hhighWindow _ hh)
  exact ⟨pool_ordered_difference_even (hpoolLow _ hl) (hpoolHigh _ hh) (le_of_lt hg.1),
    hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2⟩

/-- A fresh bridge gap extends the old complete grid and gains at least
the source's real-valued FC2K3 increment. -/
theorem bridge_extends_even_grid {α : Type*} [DecidableEq α]
    (S : Finset α) (gap : α → ℕ) (radius : ℕ) (label : α) (X : ℝ)
    (hfresh : label ∉ S)
    (hradius : 2 ∣ radius) (heven : 2 ∣ gap label)
    (hlower : bridgeGapLower X radius < (gap label : ℝ))
    (hupper : (gap label : ℝ) ≤ radius) (hgrid : CompleteEvenGrid S gap radius) :
    CompleteEvenGrid (insert label S) gap (radius + gap label) ∧
      (radius : ℝ) + bridgeGapLower X radius < ((radius + gap label : ℕ) : ℝ) := by
  have hle : gap label ≤ radius := by exact_mod_cast hupper
  refine ⟨completeEvenGrid_insert S gap radius label hfresh hradius heven (by omega) hgrid, ?_⟩
  push_cast
  linarith

/-- The source radius is only a lower bound for the actual integer grid.
A bridge gap below that lower bound still joins the actual grid, and the
new actual radius exceeds the updated source radius. -/
theorem bridge_extends_grid_from_lower_bound {α : Type*} [DecidableEq α]
    (S : Finset α) (gap : α → ℕ) (radius : ℕ) (label : α) (X R : ℝ)
    (hfresh : label ∉ S) (hradius : 2 ∣ radius) (heven : 2 ∣ gap label)
    (hcoverage : R ≤ (radius : ℝ))
    (hlower : bridgeGapLower X R < (gap label : ℝ))
    (hupper : (gap label : ℝ) ≤ R) (hgrid : CompleteEvenGrid S gap radius) :
    CompleteEvenGrid (insert label S) gap (radius + gap label) ∧
      R + bridgeGapLower X R < ((radius + gap label : ℕ) : ℝ) := by
  have hle : gap label ≤ radius := by exact_mod_cast (le_trans hupper hcoverage)
  refine ⟨completeEvenGrid_insert S gap radius label hfresh hradius heven (by omega) hgrid, ?_⟩
  push_cast
  linarith

/-- FC2K's uniform lower bound Wb for an actual modulus-two prime stock. -/
def bridgeStockBound (X R : ℝ) : ℝ :=
  (bridgeWidth X R - 2 * (518 / 125 : ℝ) * Real.sqrt (3 * X / 4)) / Real.log X

/-- A bridge-side interval under 3X/4 has the source's uniform prime
count, with the BMOR theorem and the RS index upper bound explicit. -/
theorem bmor_bridge_interval_stock (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (b c H : ℝ) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hc : c ≤ 3 * (poolMaximum n : ℝ) / 4)
    (hwidth : c - b = H) :
    (H - 2 * (518 / 125 : ℝ) * Real.sqrt (3 * (poolMaximum n : ℝ) / 4)) /
        Real.log (poolMaximum n : ℝ) ≤ (apInterval b c 2 1).card ∧
      ∀ p ∈ apInterval b c 2 1, p ∈ pool n := by
  have hX : (1 : ℝ) < (poolMaximum n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (poolMaximum_prime n).two_le)
  have hcX : c ≤ (poolMaximum n : ℝ) := by linarith
  have hstock := bmor_two_pool_interval_supply bmor upper n b c hn hnmax hb hbc hcX
  have hsb : Real.sqrt b ≤ Real.sqrt (3 * (poolMaximum n : ℝ) / 4) :=
    Real.sqrt_le_sqrt (le_trans hbc hc)
  have hsc : Real.sqrt c ≤ Real.sqrt (3 * (poolMaximum n : ℝ) / 4) :=
    Real.sqrt_le_sqrt hc
  have hnum : H - 2 * (518 / 125 : ℝ) * Real.sqrt (3 * (poolMaximum n : ℝ) / 4) ≤
      (c - b) - (518 / 125 : ℝ) * (Real.sqrt b + Real.sqrt c) := by
    rw [hwidth]
    linarith
  have hquot := div_le_div_of_nonneg_right hnum (le_of_lt (Real.log_pos hX))
  exact ⟨hquot.trans hstock.1, hstock.2⟩

def bridgeLowStock (X R : ℝ) : Finset ℕ :=
  apInterval (bridgeLowStart X R) (bridgeLowEnd X R) 2 1

def bridgeHighStock (X R : ℝ) : Finset ℕ :=
  apInterval (bridgeHighStart X R) (bridgeHighEnd X R) 2 1

/-- Both actual bridge windows have the uniform FC2K4 lower count and
consist solely of members of the prescribed pool. -/
theorem bmor_bridge_stocks (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (R : ℝ) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hR : 0 < R) :
    let X : ℝ := poolMaximum n
    bridgeStockBound X R ≤ (bridgeLowStock X R).card ∧
      bridgeStockBound X R ≤ (bridgeHighStock X R).card ∧
      (∀ p ∈ bridgeLowStock X R, p ∈ pool n) ∧
      (∀ p ∈ bridgeHighStock X R, p ∈ pool n) := by
  let X : ℝ := poolMaximum n
  have hXnat : 4 ≤ poolMaximum n := by
    have hindex : 1 < n * n := by nlinarith
    have hnth := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) hindex
    have hthree : Nat.nth Nat.Prime 1 = 3 := primeOneBased_two
    rw [hthree] at hnth
    change 3 < poolMaximum n at hnth
    omega
  have hX4 : (4 : ℝ) ≤ X := by
    change (4 : ℝ) ≤ (poolMaximum n : ℝ)
    exact_mod_cast hXnat
  have hX : 0 < X := by linarith
  have hg := bridge_window_geometry X R hX hR
  have hlow := bmor_bridge_interval_stock bmor upper n (bridgeLowStart X R)
    (bridgeLowEnd X R) (bridgeWidth X R) hn hnmax
    (by linarith [hg.2.2.1]) (le_of_lt hg.2.2.2.1)
    (by linarith [hg.2.2.2.2.1, hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1])
    hg.2.2.2.2.2.2.2.1
  have hhigh := bmor_bridge_interval_stock bmor upper n (bridgeHighStart X R)
    (bridgeHighEnd X R) (bridgeWidth X R) hn hnmax
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
    (le_of_lt hg.2.2.2.2.2.1) hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2
  exact ⟨hlow.1, hhigh.1, hlow.2, hhigh.2⟩

/-- BMOR supplies the actual bridge stocks; exact intersections charge only
reserved entries lying on each side. The numerical budgets remain explicit. -/
theorem bmor_bridge_select_pool_blocks (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (R : ℝ) (reserved : Finset ℕ) (M k : ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hR : 0 < R)
    (hbudgetLow : ((M + 2 * k +
      (bridgeLowStock (poolMaximum n) R ∩ reserved).card : ℕ) : ℝ) ≤
        bridgeStockBound (poolMaximum n) R)
    (hbudgetHigh : ((M + 2 * k +
      (bridgeHighStock (poolMaximum n) R ∩ reserved).card : ℕ) : ℝ) ≤
        bridgeStockBound (poolMaximum n) R)
    (hgate : bridgeWidth (poolMaximum n) R + 1 < (M : ℝ) * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid (bridgeLowStock (poolMaximum n) R \ reserved)
        (bridgeHighStock (poolMaximum n) R \ reserved)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, 2 ∣ b.high₁ - b.low₁ ∧
        bridgeGapLower (poolMaximum n) R < ((b.high₁ - b.low₁ : ℕ) : ℝ) ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) < bridgeSpan (poolMaximum n) R ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) ≤ R) := by
  let X : ℝ := poolMaximum n
  let low := bridgeLowStock X R
  let high := bridgeHighStock X R
  have hX : 0 < X := by
    change (0 : ℝ) < (poolMaximum n : ℝ)
    exact_mod_cast (poolMaximum_prime n).pos
  have hg := bridge_window_geometry X R hX hR
  have hlowWindow : ∀ a ∈ low,
      bridgeLowStart X R < (a : ℝ) ∧ (a : ℝ) ≤ bridgeLowEnd X R := by
    intro a ha
    have h := (mem_apInterval_iff (bridgeLowStart X R) (bridgeLowEnd X R) 2 1
      (by linarith [hg.2.2.1]) (by linarith [hg.2.2.1, hg.2.2.2.1]) a).mp ha
    exact ⟨h.2.1, h.2.2.1⟩
  have hhighWindow : ∀ b ∈ high,
      bridgeHighStart X R < (b : ℝ) ∧ (b : ℝ) ≤ bridgeHighEnd X R := by
    intro b hb
    have h := (mem_apInterval_iff (bridgeHighStart X R) (bridgeHighEnd X R) 2 1
      (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
      (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]) b).mp hb
    exact ⟨h.2.1, h.2.2.1⟩
  have hstock := bmor_bridge_stocks bmor upper n R hn hnmax hR
  have hlow : M + 2 * k + (low ∩ reserved).card ≤ low.card := by
    have hreal : ((M + 2 * k + (low ∩ reserved).card : ℕ) : ℝ) ≤ (low.card : ℝ) :=
      le_trans hbudgetLow hstock.1
    exact_mod_cast hreal
  have hhigh : M + 2 * k + (high ∩ reserved).card ≤ high.card := by
    have hreal : ((M + 2 * k + (high ∩ reserved).card : ℕ) : ℝ) ≤ (high.card : ℝ) :=
      le_trans hbudgetHigh hstock.2.1
    exact_mod_cast hreal
  obtain ⟨blocks, hlen, hvalid, hpair, hgap⟩ :=
    bridge_select_pool_blocks X R hX hR low high (low ∩ reserved) (high ∩ reserved) M k
      hstock.2.2.1 hstock.2.2.2 hlowWindow hhighWindow hlow hhigh hgate
  have hl : low \ (low ∩ reserved) = low \ reserved := by ext x; simp
  have hh : high \ (high ∩ reserved) = high \ reserved := by ext x; simp
  refine ⟨blocks, hlen, ?_, hpair, hgap⟩
  intro b hb
  simpa only [hl, hh] using hvalid b hb

end
end Sude
