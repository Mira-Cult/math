import Sude.BMORFinite
import Mathlib.Data.Int.ModEq

/-! Finite, half-open arithmetic-progression intervals used in S18.5. -/
namespace Sude
noncomputable section

/-- The actual primes in (b,c] in the residue class a mod q. -/
def apInterval (b c : ℝ) (q : ℕ) (a : ℤ) : Finset ℕ :=
  (Finset.Ico (⌊b⌋₊ + 1) (⌊c⌋₊ + 1)).filter
    (fun p => Nat.Prime p ∧ (p : ℤ) % (q : ℤ) = a % (q : ℤ))

theorem mem_apInterval_iff (b c : ℝ) (q : ℕ) (a : ℤ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (p : ℕ) :
    p ∈ apInterval b c q a ↔
      Nat.Prime p ∧ b < (p : ℝ) ∧ (p : ℝ) ≤ c ∧
        (p : ℤ) % (q : ℤ) = a % (q : ℤ) := by
  have hleft : ⌊b⌋₊ < p ↔ b < (p : ℝ) := by
    simpa only [not_le] using not_congr (Nat.le_floor_iff hb : p ≤ ⌊b⌋₊ ↔ (p : ℝ) ≤ b)
  simp only [apInterval, Finset.mem_filter, Finset.mem_Ico,
    Nat.succ_le_iff, Nat.lt_succ_iff, hleft, Nat.le_floor_iff hc]
  tauto

/-- Provided the residue class excludes 2, the actual interval primes
    below the largest pool entry are distinct members of the prescribed pool. -/
theorem apInterval_subset_pool (n : ℕ) (b c : ℝ) (q : ℕ) (a : ℤ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ≤ (poolMaximum n : ℝ))
    (hnot2 : (2 : ℤ) % (q : ℤ) ≠ a % (q : ℤ)) :
    ∀ p ∈ apInterval b c q a, p ∈ pool n := by
  intro p hp
  have hm := (mem_apInterval_iff b c q a hb hc p).mp hp
  have hne : p ≠ 2 := by
    intro h
    subst p
    exact hnot2 hm.2.2.2
  have hpmax : p ≤ poolMaximum n := by
    exact_mod_cast (le_trans hm.2.2.1 hcap)
  exact prime_mem_pool_of_le_max hm.1 hne hpmax

/-- Every reduced class modulo an even number excludes the prime 2. -/
theorem even_reduced_class_excludes_two (q : ℕ) (a : ℤ)
    (heven : 2 ∣ q) (ha : Nat.Coprime q a.natAbs) :
    (2 : ℤ) % (q : ℤ) ≠ a % (q : ℤ) := by
  intro h
  have hdivZ : (2 : ℤ) ∣ (q : ℤ) := by exact_mod_cast heven
  have hmod : Int.ModEq (q : ℤ) 2 a := h
  have hmod2 : Int.ModEq 2 2 a := Int.ModEq.of_dvd hdivZ hmod
  have hadiv : (2 : ℤ) ∣ a := by
    apply Int.dvd_iff_emod_eq_zero.mpr
    change (2 : ℤ) % 2 = a % 2 at hmod2
    norm_num at hmod2
    omega
  have hnat : 2 ∣ a.natAbs := by
    have hd := Int.natAbs_dvd_natAbs.mpr hadiv
    simpa using hd
  have bad := Nat.eq_one_of_dvd_coprimes ha heven hnat
  omega

/-- The interval primes selected by any reduced even class are actual
    entries of the prescribed pool, provided c ≤ X. -/
theorem even_apInterval_subset_pool (n : ℕ) (b c : ℝ) (q : ℕ) (a : ℤ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ≤ (poolMaximum n : ℝ))
    (heven : 2 ∣ q) (ha : Nat.Coprime q a.natAbs) :
    ∀ p ∈ apInterval b c q a, p ∈ pool n :=
  apInterval_subset_pool n b c q a hb hc hcap
    (even_reduced_class_excludes_two q a heven ha)

/-- Subtracting the two exact prefix sums leaves precisely the prime weights
    in (b,c]; no primality or prime-count estimate is assumed. -/
theorem thetaAP_sub_eq_interval_sum (b c : ℝ) (q : ℕ) (a : ℤ)
    (hbc : b ≤ c) :
    thetaAP c q a - thetaAP b q a =
      ∑ p ∈ apInterval b c q a, Real.log p := by
  classical
  let w : ℕ → ℝ := fun p =>
    if Nat.Prime p ∧ (p : ℤ) % (q : ℤ) = a % (q : ℤ) then Real.log p else 0
  have hfloor : ⌊b⌋₊ + 1 ≤ ⌊c⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_mono hbc) 1
  have hsum := Finset.sum_range_add_sum_Ico w hfloor
  have hfilter : (∑ p ∈ Finset.Ico (⌊b⌋₊ + 1) (⌊c⌋₊ + 1), w p) =
      ∑ p ∈ apInterval b c q a, Real.log p := by
    simp [apInterval, w, Finset.sum_filter]
  change (∑ p ∈ Finset.range (⌊c⌋₊ + 1), w p) -
    (∑ p ∈ Finset.range (⌊b⌋₊ + 1), w p) = _
  linarith

/-- Every weight in the actual interval is at most log X. -/
theorem thetaAP_interval_le_count_log (b c X : ℝ) (q : ℕ) (a : ℤ)
    (hb : 0 ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) :
    thetaAP c q a - thetaAP b q a ≤
      ((apInterval b c q a).card : ℝ) * Real.log X := by
  rw [thetaAP_sub_eq_interval_sum b c q a hbc]
  calc
    (∑ p ∈ apInterval b c q a, Real.log p) ≤
        ∑ _p ∈ apInterval b c q a, Real.log X := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := (mem_apInterval_iff b c q a hb (le_trans hb hbc) p).mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hm.1.pos
      exact Real.log_le_log hp0 (le_trans hm.2.2.1 hcX)
    _ = ((apInterval b c q a).card : ℝ) * Real.log X := by simp

/-- S18.5's real-variable reduction. Endpoint errors are hypotheses here;
    the resulting cardinality refers to genuine distinct interval primes. -/
theorem interval_count_from_theta_bounds (b c X : ℝ) (q : ℕ) (a : ℤ) (C : ℝ)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) (hX : 1 < X)
    (hphi : (0 : ℝ) < (Nat.totient q : ℝ))
    (hB : |thetaAP b q a - b / (Nat.totient q : ℝ)| ≤ C * Real.sqrt b)
    (hC : |thetaAP c q a - c / (Nat.totient q : ℝ)| ≤ C * Real.sqrt c) :
    ((c - b) - (Nat.totient q : ℝ) * C * (Real.sqrt b + Real.sqrt c)) /
        ((Nat.totient q : ℝ) * Real.log X) ≤ (apInterval b c q a).card := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hden : 0 < (Nat.totient q : ℝ) * Real.log X := mul_pos hphi hlog
  have hupper := thetaAP_interval_le_count_log b c X q a (by linarith) hbc hcX
  have hdiff : c / (Nat.totient q : ℝ) - b / (Nat.totient q : ℝ) -
      C * Real.sqrt c - C * Real.sqrt b ≤ thetaAP c q a - thetaAP b q a := by
    have hCb := (abs_le.mp hC).1
    have hBu := (abs_le.mp hB).2
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hdiff (le_of_lt hphi)
  field_simp at hscaled
  apply (div_le_iff₀ hden).2
  nlinarith [mul_le_mul_of_nonneg_left hupper (le_of_lt hphi)]

/-- The published q=3..100 estimate yields S18.5 for actual finite primes. -/
theorem bmor_interval_count (h : BMORFiniteTheta) (q : ℕ) (a : ℤ)
    (b c X : ℝ) (hq : 3 ≤ q) (hqmax : q ≤ 100)
    (ha : Nat.Coprime q a.natAbs) (hb : 1 ≤ b) (hbc : b ≤ c)
    (hcX : c ≤ X) (hX : 1 < X) (hcap : X ≤ (10 ^ 13 : ℝ)) :
    ((c - b) - (Nat.totient q : ℝ) * (259 / 125 : ℝ) *
        (Real.sqrt b + Real.sqrt c)) / ((Nat.totient q : ℝ) * Real.log X) ≤
      (apInterval b c q a).card := by
  have hphi : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hB := bmor_theta_bounded h q a b hq hqmax ha hb
    (le_trans (le_trans hbc hcX) hcap)
  have hC := bmor_theta_bounded h q a c hq hqmax ha (le_trans hb hbc)
    (le_trans hcX hcap)
  exact interval_count_from_theta_bounds b c X q a (259 / 125) hb hbc hcX hX
    hphi hB hC

/-- The modulus-two range is supplied by the two q=4 classes, so this
    statement remains within their published cutoff. -/
theorem bmor_interval_count_two (h : BMORFiniteTheta) (b c X : ℝ)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) (hX : 1 < X)
    (hcap : X ≤ (4 * 10 ^ 13 : ℝ)) :
    ((c - b) - (518 / 125 : ℝ) * (Real.sqrt b + Real.sqrt c)) / Real.log X ≤
      (apInterval b c 2 1).card := by
  have hB : |thetaAP b 2 1 - b / (Nat.totient 2 : ℝ)| ≤
      (518 / 125 : ℝ) * Real.sqrt b := by
    simpa [Nat.totient_two] using
      bmor_theta_two_via_four h b hb (le_trans (le_trans hbc hcX) hcap)
  have hC : |thetaAP c 2 1 - c / (Nat.totient 2 : ℝ)| ≤
      (518 / 125 : ℝ) * Real.sqrt c := by
    simpa [Nat.totient_two] using
      bmor_theta_two_via_four h c (le_trans hb hbc) (le_trans hcX hcap)
  have hphi : (0 : ℝ) < (Nat.totient 2 : ℝ) := by norm_num [Nat.totient_two]
  have hresult := interval_count_from_theta_bounds b c X 2 1 (518 / 125)
    hb hbc hcX hX hphi hB hC
  simpa [Nat.totient_two] using hresult

/-- The remaining interval after charging a single set of already reserved
    entries. The set need not be contained in the interval or in the pool. -/
def availableInterval (b c : ℝ) (q : ℕ) (a : ℤ) (reserved : Finset ℕ) : Finset ℕ :=
  apInterval b c q a \ reserved

/-- Every deleted value is charged at most once, without assuming that the
    reserved set is disjoint from other supplies. -/
theorem availableInterval_card_lower (b c : ℝ) (q : ℕ) (a : ℤ)
    (reserved : Finset ℕ) (L : ℝ) (hL : L ≤ (apInterval b c q a).card) :
    L - reserved.card ≤ (availableInterval b c q a reserved).card := by
  have hinter : (apInterval b c q a ∩ reserved).card ≤ reserved.card :=
    Finset.card_le_card Finset.inter_subset_right
  have heq := Finset.card_sdiff_add_card_inter (apInterval b c q a) reserved
  have hnat : (apInterval b c q a).card ≤
      (availableInterval b c q a reserved).card + reserved.card := by
    dsimp [availableInterval]
    omega
  have hreal : ((apInterval b c q a).card : ℝ) ≤
      ((availableInterval b c q a reserved).card : ℝ) + reserved.card := by
    exact_mod_cast hnat
  linarith

/-- Available entries remain genuine pool members and cannot have been
    reserved already. -/
theorem availableInterval_even_subset_pool (n : ℕ) (b c : ℝ) (q : ℕ) (a : ℤ)
    (reserved : Finset ℕ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcap : c ≤ (poolMaximum n : ℝ)) (heven : 2 ∣ q)
    (ha : Nat.Coprime q a.natAbs) :
    ∀ p ∈ availableInterval b c q a reserved, p ∈ pool n ∧ p ∉ reserved := by
  intro p hp
  have hm := Finset.mem_sdiff.mp hp
  exact ⟨even_apInterval_subset_pool n b c q a hb hc hcap heven ha p hm.1, hm.2⟩

/-- Bounded-range entry supply in a reduced even class. Every counted prime
    is an actual distinct member of the prescribed input pool. No prior
    reservations or deletion budget are included. -/
theorem bmor_even_pool_interval_supply (h : BMORFiniteTheta)
    (upper : RSIndexUpper) (n q : ℕ) (a : ℤ) (b c : ℝ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hq : 3 ≤ q) (hqmax : q ≤ 100)
    (heven : 2 ∣ q) (ha : Nat.Coprime q a.natAbs)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hcX : c ≤ (poolMaximum n : ℝ)) :
    ((c - b) - (Nat.totient q : ℝ) * (259 / 125 : ℝ) *
      (Real.sqrt b + Real.sqrt c)) /
        ((Nat.totient q : ℝ) * Real.log (poolMaximum n : ℝ)) ≤
      (apInterval b c q a).card ∧
    ∀ p ∈ apInterval b c q a, p ∈ pool n := by
  have hXgt : (1 : ℝ) < (poolMaximum n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (poolMaximum_prime n).two_le)
  have hXcap : (poolMaximum n : ℝ) ≤ (10 ^ 13 : ℝ) := by
    have hnat : poolMaximum n < 10 ^ 13 :=
      lt_trans (poolMaximum_below_two_pow_41 upper n hn hnmax) (by decide)
    exact_mod_cast (le_of_lt hnat)
  refine ⟨bmor_interval_count h q a b c (poolMaximum n) hq hqmax ha hb hbc hcX
    hXgt hXcap, ?_⟩
  exact even_apInterval_subset_pool n b c q a (by linarith) (by linarith) hcX heven ha

/-- The q=2 supply uses the same input pool and the q=4 class split. -/
theorem bmor_two_pool_interval_supply (h : BMORFiniteTheta)
    (upper : RSIndexUpper) (n : ℕ) (b c : ℝ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hcX : c ≤ (poolMaximum n : ℝ)) :
    ((c - b) - (518 / 125 : ℝ) * (Real.sqrt b + Real.sqrt c)) /
      Real.log (poolMaximum n : ℝ) ≤ (apInterval b c 2 1).card ∧
    ∀ p ∈ apInterval b c 2 1, p ∈ pool n := by
  have hXgt : (1 : ℝ) < (poolMaximum n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (poolMaximum_prime n).two_le)
  have hXcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ) := by
    have hnat : poolMaximum n < 4 * 10 ^ 13 :=
      lt_trans (poolMaximum_below_two_pow_41 upper n hn hnmax) (by decide)
    exact_mod_cast (le_of_lt hnat)
  refine ⟨bmor_interval_count_two h b c (poolMaximum n) hb hbc hcX hXgt hXcap, ?_⟩
  exact even_apInterval_subset_pool n b c 2 1 (by linarith) (by linarith) hcX
    (by decide) (by decide)

/-- Even-class supply after charging the full set of prior reservations. -/
theorem bmor_even_available_pool_supply (h : BMORFiniteTheta)
    (upper : RSIndexUpper) (n q : ℕ) (a : ℤ) (b c : ℝ) (reserved : Finset ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hq : 3 ≤ q) (hqmax : q ≤ 100)
    (heven : 2 ∣ q) (ha : Nat.Coprime q a.natAbs)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hcX : c ≤ (poolMaximum n : ℝ)) :
    ((c - b) - (Nat.totient q : ℝ) * (259 / 125 : ℝ) *
      (Real.sqrt b + Real.sqrt c)) /
        ((Nat.totient q : ℝ) * Real.log (poolMaximum n : ℝ)) - reserved.card ≤
      (availableInterval b c q a reserved).card ∧
    ∀ p ∈ availableInterval b c q a reserved, p ∈ pool n ∧ p ∉ reserved := by
  have hs := bmor_even_pool_interval_supply h upper n q a b c hn hnmax hq hqmax
    heven ha hb hbc hcX
  refine ⟨availableInterval_card_lower b c q a reserved _ hs.1, ?_⟩
  intro p hp
  have hm := Finset.mem_sdiff.mp hp
  exact ⟨hs.2 p hm.1, hm.2⟩

/-- Modulus-two supply after charging the full set of prior reservations. -/
theorem bmor_two_available_pool_supply (h : BMORFiniteTheta)
    (upper : RSIndexUpper) (n : ℕ) (b c : ℝ) (reserved : Finset ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hcX : c ≤ (poolMaximum n : ℝ)) :
    ((c - b) - (518 / 125 : ℝ) * (Real.sqrt b + Real.sqrt c)) /
      Real.log (poolMaximum n : ℝ) - reserved.card ≤
      (availableInterval b c 2 1 reserved).card ∧
    ∀ p ∈ availableInterval b c 2 1 reserved, p ∈ pool n ∧ p ∉ reserved := by
  have hs := bmor_two_pool_interval_supply h upper n b c hn hnmax hb hbc hcX
  refine ⟨availableInterval_card_lower b c 2 1 reserved _ hs.1, ?_⟩
  intro p hp
  have hm := Finset.mem_sdiff.mp hp
  exact ⟨hs.2 p hm.1, hm.2⟩

end
end Sude
