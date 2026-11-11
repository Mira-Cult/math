import Sude.FWBridgeBatch

/-! Actual FW source-width stocks and selection with paid deletions. -/
namespace Sude
noncomputable section

/-- Prime stocks in the FW `23/462` half-open reflected windows. -/
def fwBridgeLowStock (X R : ℝ) : Finset ℕ :=
  apInterval (fwBridgeLowStart X R) (fwBridgeLowEnd X R) 2 1

def fwBridgeHighStock (X R : ℝ) : Finset ℕ :=
  apInterval (fwBridgeHighStart X R) (fwBridgeHighEnd X R) 2 1

/-- A common BMOR lower bound using FW's source width. -/
def fwBridgeStockBound (X R : ℝ) : ℝ :=
  (fwBridgeWidth X R - 2 * (518 / 125 : ℝ) * Real.sqrt (3 * X / 4)) / Real.log X

/-- The two actual FW stocks have the stated BMOR lower count and lie in
the prescribed pool, under the explicit published analytic hypotheses. -/
theorem bmor_fw_bridge_stocks (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (R : ℝ) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hR : 0 < R) :
    let X : ℝ := poolMaximum n
    fwBridgeStockBound X R ≤ (fwBridgeLowStock X R).card ∧
      fwBridgeStockBound X R ≤ (fwBridgeHighStock X R).card ∧
      (∀ p ∈ fwBridgeLowStock X R, p ∈ pool n) ∧
      (∀ p ∈ fwBridgeHighStock X R, p ∈ pool n) := by
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
  have hg := fw_bridge_window_geometry X R hX hR
  have hlow := bmor_bridge_interval_stock bmor upper n (fwBridgeLowStart X R)
    (fwBridgeLowEnd X R) (fwBridgeWidth X R) hn hnmax
    (by linarith [hg.2.2.1]) (le_of_lt hg.2.2.2.1)
    (by linarith [hg.2.2.2.2.1, hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1])
    hg.2.2.2.2.2.2.2.1
  have hhigh := bmor_bridge_interval_stock bmor upper n (fwBridgeHighStart X R)
    (fwBridgeHighEnd X R) (fwBridgeWidth X R) hn hnmax
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
    (le_of_lt hg.2.2.2.2.2.1) hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2
  exact ⟨hlow.1, hhigh.1, hlow.2, hhigh.2⟩

/-- The source-width FW bridge stocks supply a disjoint block batch after
charging actual same-side intersections with a global reservation. Every
selected footprint avoids the whole reservation. The per-side numerical
bounds and square gate remain explicit, unproved internal obligations. -/
theorem bmor_fw_bridge_select_pool_blocks (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (R : ℝ) (reserved : Finset ℕ) (M k : ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hR : 0 < R)
    (hbudgetLow : ((M + 2 * k +
      (fwBridgeLowStock (poolMaximum n) R ∩ reserved).card : ℕ) : ℝ) ≤
        fwBridgeStockBound (poolMaximum n) R)
    (hbudgetHigh : ((M + 2 * k +
      (fwBridgeHighStock (poolMaximum n) R ∩ reserved).card : ℕ) : ℝ) ≤
        fwBridgeStockBound (poolMaximum n) R)
    (hgate : fwBridgeWidth (poolMaximum n) R + 1 < (M : ℝ) * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid (fwBridgeLowStock (poolMaximum n) R \ reserved)
        (fwBridgeHighStock (poolMaximum n) R \ reserved)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, Disjoint b.footprint reserved) ∧
      (∀ b ∈ blocks, 0 < b.high₁ - b.low₁ ∧ 2 ∣ b.high₁ - b.low₁ ∧
        (208 / 231 : ℝ) * bridgeSpan (poolMaximum n) R < ((b.high₁ - b.low₁ : ℕ) : ℝ) ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) < bridgeSpan (poolMaximum n) R ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) ≤ R) := by
  let X : ℝ := poolMaximum n
  let low := fwBridgeLowStock X R
  let high := fwBridgeHighStock X R
  have hX : 0 < X := by
    change (0 : ℝ) < (poolMaximum n : ℝ)
    exact_mod_cast (poolMaximum_prime n).pos
  have hg := fw_bridge_window_geometry X R hX hR
  have hlowWindow : ∀ a ∈ low,
      fwBridgeLowStart X R < (a : ℝ) ∧ (a : ℝ) ≤ fwBridgeLowEnd X R := by
    intro a ha
    have h := (mem_apInterval_iff (fwBridgeLowStart X R) (fwBridgeLowEnd X R) 2 1
      (by linarith [hg.2.2.1]) (by linarith [hg.2.2.1, hg.2.2.2.1]) a).mp ha
    exact ⟨h.2.1, h.2.2.1⟩
  have hhighWindow : ∀ b ∈ high,
      fwBridgeHighStart X R < (b : ℝ) ∧ (b : ℝ) ≤ fwBridgeHighEnd X R := by
    intro b hb
    have h := (mem_apInterval_iff (fwBridgeHighStart X R) (fwBridgeHighEnd X R) 2 1
      (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
      (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]) b).mp hb
    exact ⟨h.2.1, h.2.2.1⟩
  have hstock := bmor_fw_bridge_stocks bmor upper n R hn hnmax hR
  have hlow : M + 2 * k + (low ∩ reserved).card ≤ low.card := by
    have hreal : ((M + 2 * k + (low ∩ reserved).card : ℕ) : ℝ) ≤ (low.card : ℝ) :=
      le_trans hbudgetLow hstock.1
    exact_mod_cast hreal
  have hhigh : M + 2 * k + (high ∩ reserved).card ≤ high.card := by
    have hreal : ((M + 2 * k + (high ∩ reserved).card : ℕ) : ℝ) ≤ (high.card : ℝ) :=
      le_trans hbudgetHigh hstock.2.1
    exact_mod_cast hreal
  obtain ⟨blocks, hlen, hvalid, hpair, hgap⟩ :=
    fw_bridge_select_pool_blocks X R hX hR low high (low ∩ reserved) (high ∩ reserved) M k
      hstock.2.2.1 hstock.2.2.2 hlowWindow hhighWindow hlow hhigh hgate
  have hl : low \ (low ∩ reserved) = low \ reserved := by ext x; simp
  have hh : high \ (high ∩ reserved) = high \ reserved := by ext x; simp
  have hvalid' : ∀ b ∈ blocks, b.valid (low \ reserved) (high \ reserved) := by
    intro b hb
    simpa only [hl, hh] using hvalid b hb
  refine ⟨blocks, hlen, hvalid', hpair, ?_, hgap⟩
  intro b hb
  have hv := hvalid' b hb
  apply Finset.disjoint_left.mpr
  intro p hp hr
  simp only [DoublePair.footprint, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (Finset.mem_sdiff.mp hv.1).2 hr
  · exact (Finset.mem_sdiff.mp hv.2.1).2 hr
  · exact (Finset.mem_sdiff.mp hv.2.2.1).2 hr
  · exact (Finset.mem_sdiff.mp hv.2.2.2.1).2 hr

end
end Sude
