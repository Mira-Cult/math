import Sude.PrimeIndex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
BMOR Theorem 1.9's theta component and the exact modulus-two reduction.
The published theorem, including its finite computation, is an explicit
hypothesis. The pointwise estimate and class decomposition are proved here.
See `import-map.json` for the source and normalization.
-/

namespace Sude
noncomputable section

/-- The sum of logarithms of prime numbers p ≤ x in the integer class a mod q.
    For x ≥ 0, the floor and `range` implement the closed upper endpoint. -/
def thetaAP (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ Finset.range (⌊x⌋₊ + 1),
    if Nat.Prime p ∧ (p : ℤ) % (q : ℤ) = a % (q : ℤ) then Real.log p else 0

/-- The prefix set underlying `thetaAP`, useful for checking its normalization. -/
def apPrefix (x : ℝ) (q : ℕ) (a : ℤ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter
    (fun p => Nat.Prime p ∧ (p : ℤ) % (q : ℤ) = a % (q : ℤ))

theorem mem_apPrefix_iff (x : ℝ) (q : ℕ) (a : ℤ) (hx : 0 ≤ x) (p : ℕ) :
    p ∈ apPrefix x q a ↔ Nat.Prime p ∧ (p : ℝ) ≤ x ∧
      (p : ℤ) % (q : ℤ) = a % (q : ℤ) := by
  simp only [apPrefix, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff hx]
  tauto

theorem thetaAP_eq_sum_apPrefix (x : ℝ) (q : ℕ) (a : ℤ) :
    thetaAP x q a = ∑ p ∈ apPrefix x q a, Real.log p := by
  classical
  simp [thetaAP, apPrefix, Finset.sum_filter]

/-- The non-recursive base cases in BMOR equation (1.18). -/
def bmorBaseLimit (q : ℕ) : ℕ :=
  if q = 1 then 10 ^ 12
  else if q = 3 ∨ q = 4 ∨ q = 5 then 4 * 10 ^ 13
  else if q ≤ 100 then 10 ^ 13
  else if q ≤ 10 ^ 4 then 10 ^ 12
  else 10 ^ 11

/-- BMOR's x₂(q). If q ≡ 2 mod 4, q/2 is odd and one reduction
    reaches a base case. Only the published domain 1 ≤ q ≤ 10^5 is used. -/
def bmorLimit (q : ℕ) : ℕ :=
  if q % 4 = 2 then bmorBaseLimit (q / 2) else bmorBaseLimit q

@[simp] theorem bmorLimit_two : bmorLimit 2 = 10 ^ 12 := by decide
@[simp] theorem bmorLimit_four : bmorLimit 4 = 4 * 10 ^ 13 := by decide

/-- The one-step implementation agrees with the printed recursive rule. -/
theorem bmorLimit_two_mod_four (q : ℕ) (hq : q % 4 = 2) :
    bmorLimit q = bmorLimit (q / 2) := by
  have hhalf : (q / 2) % 4 ≠ 2 := by omega
  simp [bmorLimit, hq, hhalf]

/-- In the range used for bounded entry supplies, the published cutoff
    is at least 10^13; modulus 2 is intentionally excluded. -/
theorem bmorLimit_ge_ten_pow_13 {q : ℕ} (hq : 3 ≤ q) (hmax : q ≤ 100) :
    10 ^ 13 ≤ bmorLimit q := by
  unfold bmorLimit bmorBaseLimit
  split_ifs <;> norm_num at * <;> omega

/-- The theta conjunct of BMOR Theorem 1.9, expressed pointwise under its
    printed maximum. The theorem is imported, not proved or postulated globally. -/
def BMORFiniteTheta : Prop := ∀ (q : ℕ) (a : ℤ) (x y : ℝ),
  1 ≤ q → q ≤ 10 ^ 5 → Nat.Coprime q a.natAbs →
  1 ≤ y → y ≤ x → x ≤ (bmorLimit q : ℝ) →
  |thetaAP y q a - y / (Nat.totient q : ℝ)| ≤ (259 / 125 : ℝ) * Real.sqrt x

/-- Only the theta component is present so far; other published inputs
    remain to be inventoried and are not represented by this structure. -/
structure BMORFiniteImports : Prop where
  theta : BMORFiniteTheta

/-- Taking the endpoint y=x gives the pointwise theta estimate. -/
theorem bmor_theta_pointwise (h : BMORFiniteTheta) (q : ℕ) (a : ℤ) (x : ℝ)
    (hq : 1 ≤ q) (hqmax : q ≤ 10 ^ 5) (ha : Nat.Coprime q a.natAbs)
    (hx : 1 ≤ x) (hcap : x ≤ (bmorLimit q : ℝ)) :
    |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤ (259 / 125 : ℝ) * Real.sqrt x :=
  h q a x x hq hqmax ha hx le_rfl hcap

/-- Pointwise published theta estimate on the uniform q=3..100 domain. -/
theorem bmor_theta_bounded (h : BMORFiniteTheta) (q : ℕ) (a : ℤ) (x : ℝ)
    (hq : 3 ≤ q) (hqmax : q ≤ 100) (ha : Nat.Coprime q a.natAbs)
    (hx : 1 ≤ x) (hcap : x ≤ (10 ^ 13 : ℝ)) :
    |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤ (259 / 125 : ℝ) * Real.sqrt x := by
  have hlim : (10 ^ 13 : ℝ) ≤ (bmorLimit q : ℝ) := by
    exact_mod_cast bmorLimit_ge_ten_pow_13 hq hqmax
  exact bmor_theta_pointwise h q a x (by omega) (by omega) ha hx (le_trans hcap hlim)

/-- Each odd integer belongs to exactly one of the 1 and 3 classes mod 4.
    The identity is literal, including all finite endpoint contributions. -/
theorem thetaAP_two_eq_four_classes (x : ℝ) :
    thetaAP x 2 1 = thetaAP x 4 1 + thetaAP x 4 3 := by
  classical
  unfold thetaAP
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hm2 : ((p : ℤ) % 2 = 1) ↔ p % 2 = 1 := by exact_mod_cast Iff.rfl
  have hm41 : ((p : ℤ) % 4 = 1) ↔ p % 4 = 1 := by exact_mod_cast Iff.rfl
  have hm43 : ((p : ℤ) % 4 = 3) ↔ p % 4 = 3 := by exact_mod_cast Iff.rfl
  have hsplit : p % 2 = 1 ↔ p % 4 = 1 ∨ p % 4 = 3 := by omega
  by_cases hpprime : Nat.Prime p
  · by_cases h1 : p % 4 = 1
    · have h2 : p % 2 = 1 := hsplit.mpr (Or.inl h1)
      simp [hpprime, hm2, hm41, hm43, h1, h2]
    · by_cases h3 : p % 4 = 3
      · have h2 : p % 2 = 1 := hsplit.mpr (Or.inr h3)
        simp [hpprime, hm2, hm41, hm43, h2, h3]
      · have h2 : p % 2 ≠ 1 := by simp [hsplit, h1, h3]
        simp [hpprime, hm2, hm41, hm43, h1, h2, h3]
  · simp [hpprime]

/-- The modulus-two estimate uses the two modulus-four classes; its range
    is the modulus-four range, not a misstatement of BMOR's q=2 cutoff. -/
theorem bmor_theta_two_via_four (h : BMORFiniteTheta) (x : ℝ)
    (hx : 1 ≤ x) (hcap : x ≤ (4 * 10 ^ 13 : ℝ)) :
    |thetaAP x 2 1 - x| ≤ (518 / 125 : ℝ) * Real.sqrt x := by
  have hc : x ≤ (bmorLimit 4 : ℝ) := by
    rw [bmorLimit_four]
    norm_num at hcap ⊢
    exact hcap
  have hphi : Nat.totient 4 = 2 := by decide
  have h1 : |thetaAP x 4 1 - x / 2| ≤ (259 / 125 : ℝ) * Real.sqrt x := by
    have hraw := bmor_theta_pointwise h 4 1 x (by decide) (by decide) (by decide) hx hc
    simpa [hphi] using hraw
  have h3 : |thetaAP x 4 3 - x / 2| ≤ (259 / 125 : ℝ) * Real.sqrt x := by
    have hraw := bmor_theta_pointwise h 4 3 x (by decide) (by decide) (by decide) hx hc
    simpa [hphi] using hraw
  have heq : thetaAP x 2 1 - x =
      (thetaAP x 4 1 - x / 2) + (thetaAP x 4 3 - x / 2) := by
    have hsplit := thetaAP_two_eq_four_classes x
    linarith
  calc
    |thetaAP x 2 1 - x| =
        |(thetaAP x 4 1 - x / 2) + (thetaAP x 4 3 - x / 2)| := by rw [heq]
    _ ≤ |thetaAP x 4 1 - x / 2| + |thetaAP x 4 3 - x / 2| := abs_add_le _ _
    _ ≤ (518 / 125 : ℝ) * Real.sqrt x := by linarith

end
end Sude
