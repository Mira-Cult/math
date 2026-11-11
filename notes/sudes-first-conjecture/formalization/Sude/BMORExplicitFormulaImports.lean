import Sude.BMORFinite
import Sude.T75ThetaIntervalBrackets
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Source-Faithful BMOR Explicit Formula and RS62 Prime-Power Imports

Encodes the published explicit-formula, zero-verification, and prime-power
inputs from:
1. Rosser–Schoenfeld (1962), Theorem 4, equation `(3.15)`, printed p. 70:
   `θ(t) < t + t / (2 * log t)` for `t > 1`.
2. Bennett–Martin–O'Bryant–Rechnitzer (2018), Proposition 2.1 `(2.3)`–`(2.7)`
   (pp. 438–439), Proposition 2.5 (p. 441), Proposition 2.7 (p. 441),
   Lemma 2.11 (pp. 442–443), and Proposition 4.34 (pp. 478–479).

From these explicit hypotheses, this module proves:
- Proper prime-power nonnegativity and envelope domination (`S18.22`).
- The pointwise low-zero progression error bound `(S18.24)` / `(TL14)` for
  small moduli `3 ≤ q ≤ Q ≤ 100000`.
- The pointwise parity error bound `(S18.30)` for `q = 2, a = 1`.
- The exact interval equality (`TL4`) between modulus `42` and modulus `21`
  for odd reduced classes on intervals above `2`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 4000000

/-- Sum of `log p` over primes `p ≤ x^(1/k)` with `p^k ≡ a (mod q)`. -/
def thetaPowerAP (x : ℝ) (k q : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ Finset.range (⌊x ^ (1 / (k : ℝ))⌋₊ + 1),
    if Nat.Prime p ∧ ((p ^ k : ℕ) : ℤ) % (q : ℤ) = a % (q : ℤ) then Real.log p else 0

/-- Proper prime-power contribution `ψ(x; q, a) - θ(x; q, a)`, summing `thetaPowerAP x k q a`
    over exponents `2 ≤ k ≤ ⌊log x / log 2⌋₊`. -/
def psiProperAP (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊, thetaPowerAP x k q a

/-- Chebyshev's prime-power sum `ψ(x; q, a) = θ(x; q, a) + psiProperAP x q a`. -/
def psiAP (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  thetaAP x q a + psiProperAP x q a

/-- Envelope `θ(√x) + θ(x^(1/3)) + (log x / log 2) * θ(x^(1/4))` bounding `psiProperAP x q a`. -/
def psiProperEnvelope (x : ℝ) : ℝ :=
  thetaAP (Real.sqrt x) 1 0 +
  thetaAP (x ^ (1 / 3 : ℝ)) 1 0 +
  (Real.log x / Real.log 2) * thetaAP (x ^ (1 / 4 : ℝ)) 1 0

/-- Rosser–Schoenfeld (1962), Theorem 4, equation (3.15), printed p. 70:
    for every real `t > 1`, `θ(t) < t + t / (2 * log t)`. -/
def RSThetaUpper : Prop :=
  ∀ t : ℝ, 1 < t → thetaAP t 1 0 < t + t / (2 * Real.log t)

/-- BMOR Definition 2.4 and Proposition 2.5, printed p. 441: `C₁ = 0.399`. -/
def bmorC1 : ℝ := 399 / 1000

/-- BMOR Definition 2.4 and Proposition 2.5, printed p. 441: `C₂ = 5.338`. -/
def bmorC2 : ℝ := 5338 / 1000

/-- BMOR Definition 3.1 (p. 451) and Proposition 4.34 (pp. 478–479):
    unconditional zero-free region constant `R = 5.6 = 28/5`. -/
def bmorZeroFreeR : ℝ := 28 / 5

/-- Verified critical-line height `H₀(d)` in BMOR Definition 2.6 and Proposition 2.7, p. 441:
    `30610046000` for `d = 1` and `10^8 / d` for `1 < d ≤ 100000`. -/
def bmorVerifiedHeight (d : ℕ) : ℝ :=
  if d = 1 then 30610046000
  else if d ≤ 100000 then (10 ^ 8 : ℝ) / (d : ℝ)
  else 0

/-- Smoothing factor `A_r(τ) = τ⁻ʳ ∑_{j=0}^r C(r, j) (1 + j τ)^{r+1}` from BMOR Proposition 2.1 (2.4). -/
def bmorSmoothFactor (r : ℕ) (τ : ℝ) : ℝ :=
  (τ ^ r)⁻¹ * ∑ j ∈ Finset.range (r + 1),
    (Nat.choose r j : ℝ) * (1 + (j : ℝ) * τ) ^ (r + 1)

/-- Signed low-zero reciprocal sum upper bound `K(Q, H)` from BMOR Proposition 2.5 and
    Lemma 2.11, equation (LZ3). -/
def bmorLowZeroCap (Q H : ℝ) : ℝ :=
  let ν := Real.log Q
  let lam := Real.log (Q * H)
  let c := Real.log (2 * Real.pi) + 1
  (((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi) +
    2 * bmorC1 * ν + bmorC1 + 2 * bmorC2 - bmorC1 / H

/-- High-zero spectral sum bound `S_z` over characters modulo `q ≤ Q` with `φ(q) ≤ Φ`,
    for `H = 10^8 / Q`, `λ = log(10^8)`, `a_r = r - z / (R * λ^2) > 0`, equation (Q30.7). -/
def bmorHighZeroSum (Q Φ z : ℝ) (r : ℕ) : ℝ :=
  let H := (10 ^ 8 : ℝ) / Q
  let lam := Real.log (10 ^ 8 : ℝ)
  let ar := (r : ℝ) - z / (bmorZeroFreeR * lam ^ 2)
  let Br := (lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (bmorC1 * lam + bmorC2) / H
  let Br0 := (lam / (r : ℝ) + 1 / (r : ℝ) ^ 2) / Real.pi + 2 * (bmorC1 * lam + bmorC2) / H
  (Φ / (2 * H ^ r)) * (Real.exp (-z / (bmorZeroFreeR * lam)) * Br + Real.exp (-z / 2) * Br0)

/-- High-zero spectral sum bound `S_s` for the single non-principal character modulo `2`
    (primitive conductor `1`) above verified height `H_s < 30610046000` with `log(2 * H_s) ≤ 25`,
    equation (S18.30). -/
def bmorParityHighZeroSum (Hs : ℝ) (rs : ℕ) : ℝ :=
  (Hs ^ rs)⁻¹ * (((25 / (rs : ℝ) + 1 / (rs : ℝ) ^ 2) / Real.pi) +
    2 * (25 * bmorC1 + bmorC2) / Hs)

/-- BMOR Proposition 2.1 (2.3)–(2.7) (pp. 438–439) combined with Propositions 2.5, 2.7, 4.34
    and Lemma 2.11 for small moduli `3 ≤ q ≤ Q ≤ 100000`. -/
def BMORSmoothedPsiSmallModuli : Prop :=
  ∀ (q Q : ℕ) (a : ℤ) (r : ℕ) (τ z x : ℝ),
    3 ≤ q → q ≤ Q → Q ≤ 100000 →
    Nat.Coprime q a.natAbs →
    1 ≤ r → 0 < τ → (r : ℝ) * τ < 1 / 100 →
    14 ≤ z → 0 < (r : ℝ) - z / (bmorZeroFreeR * (Real.log (10 ^ 8 : ℝ)) ^ 2) →
    1 ≤ x → z ≤ Real.log x →
    (Nat.totient q : ℝ) * |psiAP x q a - x / (Nat.totient q : ℝ)| ≤
      ((r : ℝ) * τ / 2 + bmorSmoothFactor r τ * bmorHighZeroSum (Q : ℝ) (Nat.totient q : ℝ) z r) * x +
      (Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) ((10 ^ 8 : ℝ) / (Q : ℝ)) * (1 + (r : ℝ) * τ / 2) * Real.sqrt x +
      (Nat.totient q : ℝ) * (25 * Real.log x + 62)

/-- BMOR Proposition 2.1 (2.3)–(2.7) (pp. 438–439) combined with Propositions 2.5, 2.7
    and Lemma 2.11 for `q = 2, a = 1` (single non-principal character of primitive conductor `1`). -/
def BMORSmoothedPsiModTwo : Prop :=
  ∀ (rs : ℕ) (Hs τs zs x : ℝ),
    1 ≤ rs → 1000 ≤ Hs → Hs ≤ 30610046000 → Real.log (2 * Hs) ≤ 25 →
    0 < τs → (rs : ℝ) * τs < 1 / 100 →
    14 ≤ zs → 1 ≤ x → zs ≤ Real.log x →
    |psiAP x 2 1 - x| ≤
      ((rs : ℝ) * τs / 2 + bmorSmoothFactor rs τs * bmorParityHighZeroSum Hs rs) * x +
      bmorLowZeroCap 2 Hs * (1 + (rs : ℝ) * τs / 2) * Real.sqrt x +
      (25 * Real.log x + 62)

/-- Bundled published explicit-formula and prime-power hypotheses. -/
structure BMORExplicitFormulaImports : Prop where
  rs_theta_upper : RSThetaUpper
  smoothed_psi_small_moduli : BMORSmoothedPsiSmallModuli
  smoothed_psi_mod_two : BMORSmoothedPsiModTwo

theorem thetaAP_one_nonneg (t : ℝ) : 0 ≤ thetaAP t 1 0 := by
  unfold thetaAP
  apply Finset.sum_nonneg
  intro p _
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.1.one_lt.le)
  · rfl

theorem thetaPowerAP_nonneg (x : ℝ) (k q : ℕ) (a : ℤ) : 0 ≤ thetaPowerAP x k q a := by
  unfold thetaPowerAP
  apply Finset.sum_nonneg
  intro p _
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.1.one_lt.le)
  · rfl

theorem psiProperAP_nonneg (x : ℝ) (q : ℕ) (a : ℤ) : 0 ≤ psiProperAP x q a := by
  unfold psiProperAP
  exact Finset.sum_nonneg (fun k _ => thetaPowerAP_nonneg x k q a)

theorem psiAP_sub_thetaAP_eq (x : ℝ) (q : ℕ) (a : ℤ) :
    psiAP x q a - thetaAP x q a = psiProperAP x q a := by
  unfold psiAP
  ring

theorem thetaPowerAP_le_thetaAP_one (x : ℝ) (k q : ℕ) (a : ℤ) :
    thetaPowerAP x k q a ≤ thetaAP (x ^ (1 / (k : ℝ))) 1 0 := by
  unfold thetaPowerAP thetaAP
  apply Finset.sum_le_sum
  intro p _
  by_cases h1 : Nat.Prime p ∧ ((p ^ k : ℕ) : ℤ) % (q : ℤ) = a % (q : ℤ)
  · have h2 : Nat.Prime p ∧ (p : ℤ) % ((1 : ℕ) : ℤ) = 0 % ((1 : ℕ) : ℤ) := ⟨h1.1, by omega⟩
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1]
    split_ifs with h2
    · exact Real.log_nonneg (by exact_mod_cast h2.1.one_lt.le)
    · rfl

theorem thetaAP_one_mono {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    thetaAP t₁ 1 0 ≤ thetaAP t₂ 1 0 := by
  unfold thetaAP
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.range_mono
    exact Nat.add_le_add_right (Nat.floor_mono ht) 1
  · intro p _ _
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.1.one_lt.le)
    · rfl

/-- Proper prime powers are bounded by `psiProperEnvelope x` for `1 ≤ x`. -/
theorem psiProperAP_le_envelope {x : ℝ} (hx : 1 ≤ x) (q : ℕ) (a : ℤ) :
    psiProperAP x q a ≤ psiProperEnvelope x := by
  classical
  unfold psiProperAP psiProperEnvelope
  let N := ⌊Real.log x / Real.log 2⌋₊
  have hsub : Finset.Icc 2 N ⊆ ({2} : Finset ℕ) ∪ (({3} : Finset ℕ) ∪ Finset.Icc 4 N) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hsum_le : (∑ k ∈ Finset.Icc 2 N, thetaPowerAP x k q a) ≤
      ∑ k ∈ ({2} : Finset ℕ) ∪ (({3} : Finset ℕ) ∪ Finset.Icc 4 N), thetaPowerAP x k q a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _ _
    exact thetaPowerAP_nonneg x k q a
  have hdisj1 : Disjoint ({2} : Finset ℕ) (({3} : Finset ℕ) ∪ Finset.Icc 4 N) := by
    simp
  have hdisj2 : Disjoint ({3} : Finset ℕ) (Finset.Icc 4 N) := by
    simp
  rw [Finset.sum_union hdisj1, Finset.sum_union hdisj2,
      Finset.sum_singleton, Finset.sum_singleton] at hsum_le
  have h2 : thetaPowerAP x 2 q a ≤ thetaAP (Real.sqrt x) 1 0 := by
    have hpow := thetaPowerAP_le_thetaAP_one x 2 q a
    norm_num [Real.sqrt_eq_rpow] at hpow ⊢
    exact hpow
  have h3 : thetaPowerAP x 3 q a ≤ thetaAP (x ^ (1 / 3 : ℝ)) 1 0 := by
    simpa using thetaPowerAP_le_thetaAP_one x 3 q a
  have h4 : (∑ k ∈ Finset.Icc 4 N, thetaPowerAP x k q a) ≤
      (Real.log x / Real.log 2) * thetaAP (x ^ (1 / 4 : ℝ)) 1 0 := by
    have hterm : ∀ k ∈ Finset.Icc 4 N, thetaPowerAP x k q a ≤ thetaAP (x ^ (1 / 4 : ℝ)) 1 0 := by
      intro k hk
      have hk4 : 4 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
      have hexp : 1 / (k : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hk_real
      exact (thetaPowerAP_le_thetaAP_one x k q a).trans
        (thetaAP_one_mono (Real.rpow_le_rpow_of_exponent_le hx hexp))
    have hcard_sum : (∑ k ∈ Finset.Icc 4 N, thetaPowerAP x k q a) ≤
        ((Finset.Icc 4 N).card : ℝ) * thetaAP (x ^ (1 / 4 : ℝ)) 1 0 := by
      calc
        (∑ k ∈ Finset.Icc 4 N, thetaPowerAP x k q a)
          ≤ ∑ _k ∈ Finset.Icc 4 N, thetaAP (x ^ (1 / 4 : ℝ)) 1 0 := Finset.sum_le_sum hterm
        _ = ((Finset.Icc 4 N).card : ℝ) * thetaAP (x ^ (1 / 4 : ℝ)) 1 0 := by simp
    have hcard_le : ((Finset.Icc 4 N).card : ℝ) ≤ Real.log x / Real.log 2 := by
      rw [Nat.card_Icc]
      have hN_le : (N : ℝ) ≤ Real.log x / Real.log 2 :=
        Nat.floor_le (div_nonneg (Real.log_nonneg hx) (Real.log_nonneg (by norm_num)))
      have hsub_le : ((N + 1 - 4 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show N + 1 - 4 ≤ N by omega)
      linarith
    exact hcard_sum.trans (mul_le_mul_of_nonneg_right hcard_le (thetaAP_one_nonneg _))
  linarith

/-- Lower bound on `exp u` for `u ≥ 0` via its degree-6 Taylor polynomial. -/
private theorem exp_ge_taylor6 {u : ℝ} (hu : 0 ≤ u) :
    1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 + u ^ 6 / 720 ≤ Real.exp u := by
  have h := Real.sum_le_exp_of_nonneg hu 7
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  linarith

/-- Equation (S18.22): From `RSThetaUpper` (RS62 Theorem 4, (3.15)), for all `1 ≤ x`
    with `14 ≤ Real.log x`, `0 ≤ psiAP x q a - thetaAP x q a` and
    `psiAP x q a - thetaAP x q a < 2 * Real.sqrt x`. -/
theorem rs_proper_prime_power_bound (hrs : RSThetaUpper)
    (q : ℕ) (a : ℤ) {x : ℝ} (hx : 1 ≤ x) (hlog : 14 ≤ Real.log x) :
    0 ≤ psiAP x q a - thetaAP x q a ∧
    psiAP x q a - thetaAP x q a < 2 * Real.sqrt x ∧
    |thetaAP x q a - psiAP x q a| ≤ 2 * Real.sqrt x := by
  rw [psiAP_sub_thetaAP_eq]
  have hnonneg : 0 ≤ psiProperAP x q a := psiProperAP_nonneg x q a
  have henv : psiProperAP x q a ≤ psiProperEnvelope x := psiProperAP_le_envelope hx q a
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let t := Real.log x
  have ht : 14 ≤ t := hlog
  have hsqrt_gt : 1 < Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_zero x]
    exact Real.rpow_lt_rpow_of_exponent_lt (by
      by_contra hle; push Not at hle
      have : Real.log x ≤ 0 := Real.log_nonpos hx_pos.le hle
      linarith) (by norm_num)
  have hx1_gt : 1 < x := by
    by_contra hle; push Not at hle
    have : Real.log x ≤ 0 := Real.log_nonpos hx_pos.le hle
    linarith
  have hlog_sqrt : Real.log (Real.sqrt x) = t / 2 := Real.log_sqrt hx_pos.le
  have htheta2 : thetaAP (Real.sqrt x) 1 0 < (15 / 14 : ℝ) * Real.sqrt x := by
    have h := hrs (Real.sqrt x) hsqrt_gt
    rw [hlog_sqrt] at h
    have hdiv : Real.sqrt x / (2 * (t / 2)) ≤ (1 / 14 : ℝ) * Real.sqrt x := by
      have heq : 2 * (t / 2) = t := by ring
      rw [heq, div_eq_mul_inv]
      have hinv : t⁻¹ ≤ (14 : ℝ)⁻¹ := inv_anti₀ (by norm_num) ht
      nlinarith [Real.sqrt_pos.mpr hx_pos]
    linarith
  have hcbrt_gt : 1 < x ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_zero x]
    exact Real.rpow_lt_rpow_of_exponent_lt hx1_gt (by norm_num)
  have hlog_cbrt : Real.log (x ^ (1 / 3 : ℝ)) = t / 3 := by
    rw [Real.log_rpow hx_pos]
    ring
  have hcbrt_le : x ^ (1 / 3 : ℝ) ≤ (1 / 9 : ℝ) * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    have hsplit : (1 / 2 : ℝ) = (1 / 3 : ℝ) + (1 / 6 : ℝ) := by norm_num
    rw [hsplit, Real.rpow_add hx_pos]
    have hexp6 : (9 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
      rw [Real.rpow_def_of_pos hx_pos]
      let v := t * (1 / 6)
      have hv : 7 / 3 ≤ v := by dsimp [v]; linarith
      have htay := exp_ge_taylor6 (by linarith : (0 : ℝ) ≤ v)
      have hv2 : (7 / 3 : ℝ) ^ 2 ≤ v ^ 2 := by nlinarith
      have hv3 : (7 / 3 : ℝ) ^ 3 ≤ v ^ 3 := by nlinarith
      have hv4 : (7 / 3 : ℝ) ^ 4 ≤ v ^ 4 := by nlinarith
      have hv5 : 0 ≤ v ^ 5 := by positivity
      have hv6 : 0 ≤ v ^ 6 := by positivity
      linarith
    nlinarith [Real.rpow_pos_of_pos hx_pos (1 / 3 : ℝ)]
  have htheta3 : thetaAP (x ^ (1 / 3 : ℝ)) 1 0 < (1 / 7 : ℝ) * Real.sqrt x := by
    have h := hrs (x ^ (1 / 3 : ℝ)) hcbrt_gt
    rw [hlog_cbrt] at h
    have hdiv : x ^ (1 / 3 : ℝ) / (2 * (t / 3)) ≤ (3 / 28 : ℝ) * x ^ (1 / 3 : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.rpow_pos_of_pos hx_pos (1 / 3 : ℝ)]
    nlinarith [Real.sqrt_pos.mpr hx_pos]
  have hqdrt_gt : 1 < x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_zero x]
    exact Real.rpow_lt_rpow_of_exponent_lt hx1_gt (by norm_num)
  have hlog_qdrt : Real.log (x ^ (1 / 4 : ℝ)) = t / 4 := by
    rw [Real.log_rpow hx_pos]
    ring
  have hlog2_gt : (693147 / 1000000 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hqdrt_prod_le : (t / Real.log 2) * (x ^ (1 / 4 : ℝ) + x ^ (1 / 4 : ℝ) / (2 * (t / 4))) ≤
      (3 / 4 : ℝ) * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    have hsplit : (1 / 2 : ℝ) = (1 / 4 : ℝ) + (1 / 4 : ℝ) := by norm_num
    rw [hsplit, Real.rpow_add hx_pos]
    have hsimp : x ^ (1 / 4 : ℝ) + x ^ (1 / 4 : ℝ) / (2 * (t / 4)) =
        x ^ (1 / 4 : ℝ) * ((t + 2) / t) := by
      field_simp [show t ≠ 0 by linarith]
      ring
    rw [hsimp]
    have hprod : (t / Real.log 2) * (x ^ (1 / 4 : ℝ) * ((t + 2) / t)) =
        x ^ (1 / 4 : ℝ) * ((t + 2) / Real.log 2) := by
      field_simp [show t ≠ 0 by linarith, show Real.log 2 ≠ 0 by linarith]
    rw [hprod]
    have hexp4 : (4 / 3 : ℝ) * ((t + 2) / Real.log 2) ≤ x ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_def_of_pos hx_pos]
      let u := t * (1 / 4)
      have hu : 7 / 2 ≤ u := by dsimp [u]; linarith
      have htay := exp_ge_taylor6 (by linarith : (0 : ℝ) ≤ u)
      have hu1 : (7 / 2 : ℝ) * u ≤ u ^ 2 := by nlinarith
      have hu2 : (49 / 4 : ℝ) * u ≤ u ^ 3 := by nlinarith
      have hu3 : (343 / 8 : ℝ) * u ≤ u ^ 4 := by nlinarith
      have hu4 : (2401 / 16 : ℝ) * u ≤ u ^ 5 := by nlinarith
      have hu5 : (16807 / 32 : ℝ) * u ≤ u ^ 6 := by nlinarith
      have hlin_u : 1 + (197179 / 23040 : ℝ) * u ≤ Real.exp u := by linarith
      have hlin_t : 1 + (197179 / 92160 : ℝ) * t ≤ Real.exp (t * (1 / 4)) := by
        dsimp [u] at hlin_u
        linarith
      have hlhs : (4 / 3 : ℝ) * ((t + 2) / Real.log 2) ≤ 1 + (197179 / 92160 : ℝ) * t := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
      exact le_trans hlhs hlin_t
    nlinarith [Real.rpow_pos_of_pos hx_pos (1 / 4 : ℝ)]
  have htheta4 : (t / Real.log 2) * thetaAP (x ^ (1 / 4 : ℝ)) 1 0 < (3 / 4 : ℝ) * Real.sqrt x := by
    have h := hrs (x ^ (1 / 4 : ℝ)) hqdrt_gt
    rw [hlog_qdrt] at h
    have hmul : (t / Real.log 2) * thetaAP (x ^ (1 / 4 : ℝ)) 1 0 <
        (t / Real.log 2) * (x ^ (1 / 4 : ℝ) + x ^ (1 / 4 : ℝ) / (2 * (t / 4))) := by
      exact mul_lt_mul_of_pos_left h (div_pos (by linarith) (by linarith))
    linarith
  have hlt : psiProperAP x q a < 2 * Real.sqrt x := by
    unfold psiProperEnvelope at henv
    change thetaAP (Real.sqrt x) 1 0 + thetaAP (x ^ (1 / 3 : ℝ)) 1 0 +
      (t / Real.log 2) * thetaAP (x ^ (1 / 4 : ℝ)) 1 0 ≥ psiProperAP x q a at henv
    linarith
  refine ⟨hnonneg, hlt, ?_⟩
  have habs : |thetaAP x q a - psiAP x q a| = psiProperAP x q a := by
    rw [abs_sub_comm, psiAP_sub_thetaAP_eq, abs_of_nonneg hnonneg]
  linarith

/-- Equation (S18.24) / (TL14): Pointwise progression theta bound for `3 ≤ q ≤ Q ≤ 100000`
    derived from `BMORSmoothedPsiSmallModuli` and `RSThetaUpper`. -/
theorem bmor_theta_small_moduli_pointwise
    (imp : BMORExplicitFormulaImports)
    {q Q : ℕ} {a : ℤ} {r : ℕ} {Φ τ z K0 x : ℝ}
    (hq3 : 3 ≤ q) (hqQ : q ≤ Q) (hQ : Q ≤ 100000)
    (hcop : Nat.Coprime q a.natAbs)
    (hphi : (Nat.totient q : ℝ) ≤ Φ)
    (hr : 1 ≤ r) (hτ : 0 < τ) (hrτ : (r : ℝ) * τ < 1 / 100)
    (hz : 14 ≤ z)
    (har : 0 < (r : ℝ) - z / (bmorZeroFreeR * (Real.log (10 ^ 8 : ℝ)) ^ 2))
    (hK0 : bmorLowZeroCap (Q : ℝ) ((10 ^ 8 : ℝ) / (Q : ℝ)) ≤ K0)
    (hK0_nonneg : 0 ≤ K0)
    (hx : 1 ≤ x) (hlog : z ≤ Real.log x) :
    (Nat.totient q : ℝ) * |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤
      ((r : ℝ) * τ / 2 + bmorSmoothFactor r τ * bmorHighZeroSum (Q : ℝ) Φ z r) * x +
      Φ * (K0 * (1 + (r : ℝ) * τ / 2) + 2) * Real.sqrt x +
      Φ * (25 * Real.log x + 62) := by
  have hpsi := imp.smoothed_psi_small_moduli q Q a r τ z x hq3 hqQ hQ hcop hr hτ hrτ hz har hx hlog
  have hpp := (rs_proper_prime_power_bound imp.rs_theta_upper q a hx (le_trans hz hlog)).2.2
  have htri : |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤
      |psiAP x q a - x / (Nat.totient q : ℝ)| + |thetaAP x q a - psiAP x q a| := by
    have hid : thetaAP x q a - x / (Nat.totient q : ℝ) =
        (psiAP x q a - x / (Nat.totient q : ℝ)) + (thetaAP x q a - psiAP x q a) := by ring
    rw [hid]
    exact abs_add_le _ _
  have hphi_nonneg : (0 : ℝ) ≤ (Nat.totient q : ℝ) := Nat.cast_nonneg _
  have hmul_tri : (Nat.totient q : ℝ) * |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤
      (Nat.totient q : ℝ) * |psiAP x q a - x / (Nat.totient q : ℝ)| +
      (Nat.totient q : ℝ) * (2 * Real.sqrt x) := by
    nlinarith [mul_le_mul_of_nonneg_left htri hphi_nonneg,
               mul_le_mul_of_nonneg_left hpp hphi_nonneg]
  have hH_pos : (0 : ℝ) < (10 ^ 8 : ℝ) / (Q : ℝ) := by
    apply div_pos (by norm_num)
    exact_mod_cast (show 0 < Q by omega)
  have hlam_pos : 0 < Real.log (10 ^ 8 : ℝ) := Real.log_pos (by norm_num)
  have hBr_nonneg : 0 ≤ (Real.log (10 ^ 8 : ℝ) / ((r : ℝ) - z / (bmorZeroFreeR * (Real.log (10 ^ 8 : ℝ)) ^ 2)) +
      1 / ((r : ℝ) - z / (bmorZeroFreeR * (Real.log (10 ^ 8 : ℝ)) ^ 2)) ^ 2) / Real.pi +
      2 * (bmorC1 * Real.log (10 ^ 8 : ℝ) + bmorC2) / ((10 ^ 8 : ℝ) / (Q : ℝ)) := by
    unfold bmorC1 bmorC2
    positivity
  have hBr0_nonneg : 0 ≤ (Real.log (10 ^ 8 : ℝ) / (r : ℝ) + 1 / (r : ℝ) ^ 2) / Real.pi +
      2 * (bmorC1 * Real.log (10 ^ 8 : ℝ) + bmorC2) / ((10 ^ 8 : ℝ) / (Q : ℝ)) := by
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    unfold bmorC1 bmorC2
    positivity
  have hhigh_mono : bmorHighZeroSum (Q : ℝ) (Nat.totient q : ℝ) z r ≤ bmorHighZeroSum (Q : ℝ) Φ z r := by
    unfold bmorHighZeroSum
    dsimp only
    apply mul_le_mul_of_nonneg_right
    · exact div_le_div_of_nonneg_right hphi (by positivity)
    · positivity
  have hsmooth_nonneg : 0 ≤ bmorSmoothFactor r τ := by
    unfold bmorSmoothFactor
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro j _
    positivity
  have hlow_mono : (Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) ((10 ^ 8 : ℝ) / (Q : ℝ)) * (1 + (r : ℝ) * τ / 2) * Real.sqrt x +
      (Nat.totient q : ℝ) * (2 * Real.sqrt x) ≤
      Φ * (K0 * (1 + (r : ℝ) * τ / 2) + 2) * Real.sqrt x := by
    have hprod_le : (Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) ((10 ^ 8 : ℝ) / (Q : ℝ)) ≤ Φ * K0 :=
      (mul_le_mul_of_nonneg_left hK0 hphi_nonneg).trans (mul_le_mul_of_nonneg_right hphi hK0_nonneg)
    have hinner : (Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) ((10 ^ 8 : ℝ) / (Q : ℝ)) * (1 + (r : ℝ) * τ / 2) +
        (Nat.totient q : ℝ) * 2 ≤ Φ * (K0 * (1 + (r : ℝ) * τ / 2) + 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hprod_le (by positivity : 0 ≤ 1 + (r : ℝ) * τ / 2)]
    calc
      (Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) ((10 ^ 8 : ℝ) / (Q : ℝ)) * (1 + (r : ℝ) * τ / 2) * Real.sqrt x +
          (Nat.totient q : ℝ) * (2 * Real.sqrt x)
        = ((Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) ((10 ^ 8 : ℝ) / (Q : ℝ)) * (1 + (r : ℝ) * τ / 2) +
            (Nat.totient q : ℝ) * 2) * Real.sqrt x := by ring
      _ ≤ Φ * (K0 * (1 + (r : ℝ) * τ / 2) + 2) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hinner (Real.sqrt_nonneg x)
  have hnon_mono : (Nat.totient q : ℝ) * (25 * Real.log x + 62) ≤ Φ * (25 * Real.log x + 62) := by
    apply mul_le_mul_of_nonneg_right hphi
    linarith
  have hmain_mono : ((r : ℝ) * τ / 2 + bmorSmoothFactor r τ * bmorHighZeroSum (Q : ℝ) (Nat.totient q : ℝ) z r) * x ≤
      ((r : ℝ) * τ / 2 + bmorSmoothFactor r τ * bmorHighZeroSum (Q : ℝ) Φ z r) * x := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hhigh_mono hsmooth_nonneg]
  linarith

/-- Equation (S18.30): Pointwise parity theta bound for `q = 2, a = 1`
    derived from `BMORSmoothedPsiModTwo` and `RSThetaUpper`. -/
theorem bmor_theta_mod_two_pointwise
    (imp : BMORExplicitFormulaImports)
    {rs : ℕ} {Hs τs zs Ks x : ℝ}
    (hrs : 1 ≤ rs) (hHs_lo : 1000 ≤ Hs) (hHs_hi : Hs ≤ 30610046000)
    (hlogHs : Real.log (2 * Hs) ≤ 25)
    (hτs : 0 < τs) (hrsτs : (rs : ℝ) * τs < 1 / 100)
    (hzs : 14 ≤ zs)
    (hKs : bmorLowZeroCap 2 Hs ≤ Ks)
    (hx : 1 ≤ x) (hlog : zs ≤ Real.log x) :
    |thetaAP x 2 1 - x| ≤
      ((rs : ℝ) * τs / 2 + bmorSmoothFactor rs τs * bmorParityHighZeroSum Hs rs) * x +
      (Ks * (1 + (rs : ℝ) * τs / 2) + 2) * Real.sqrt x +
      (25 * Real.log x + 62) := by
  have hpsi := imp.smoothed_psi_mod_two rs Hs τs zs x hrs hHs_lo hHs_hi hlogHs hτs hrsτs hzs hx hlog
  have hpp := (rs_proper_prime_power_bound imp.rs_theta_upper 2 1 hx (le_trans hzs hlog)).2.2
  have htri : |thetaAP x 2 1 - x| ≤ |psiAP x 2 1 - x| + |thetaAP x 2 1 - psiAP x 2 1| := by
    have hid : thetaAP x 2 1 - x = (psiAP x 2 1 - x) + (thetaAP x 2 1 - psiAP x 2 1) := by ring
    rw [hid]
    exact abs_add_le _ _
  have hlow : bmorLowZeroCap 2 Hs * (1 + (rs : ℝ) * τs / 2) * Real.sqrt x + 2 * Real.sqrt x ≤
      (Ks * (1 + (rs : ℝ) * τs / 2) + 2) * Real.sqrt x := by
    have hinner : bmorLowZeroCap 2 Hs * (1 + (rs : ℝ) * τs / 2) + 2 ≤ Ks * (1 + (rs : ℝ) * τs / 2) + 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hKs (by positivity : 0 ≤ 1 + (rs : ℝ) * τs / 2)]
    calc
      bmorLowZeroCap 2 Hs * (1 + (rs : ℝ) * τs / 2) * Real.sqrt x + 2 * Real.sqrt x
        = (bmorLowZeroCap 2 Hs * (1 + (rs : ℝ) * τs / 2) + 2) * Real.sqrt x := by ring
      _ ≤ (Ks * (1 + (rs : ℝ) * τs / 2) + 2) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hinner (Real.sqrt_nonneg x)
  linarith

/-- Section TL4: For any reduced residue `r < 42` coprime to `42` and any interval `(a, b]`
    with `2 ≤ a ≤ b`, `apInterval a b 42 r = apInterval a b 21 (r % 21)`. -/
theorem apInterval_forty_two_eq_twenty_one {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    {r : ℕ} (hr : r < 42) (hcop : Nat.Coprime r 42) :
    apInterval a b 42 (r : ℤ) = apInterval a b 21 ((r % 21 : ℕ) : ℤ) := by
  have hr_odd : r % 2 = 1 := by
    by_contra h2
    have hdvd : 2 ∣ r := Nat.dvd_of_mod_eq_zero (by omega)
    have hdvd42 : 2 ∣ 42 := by decide
    have hdvd_gcd : 2 ∣ Nat.gcd r 42 := Nat.dvd_gcd hdvd hdvd42
    rw [hcop] at hdvd_gcd
    omega
  ext p
  rw [mem_apInterval_iff a b 42 (r : ℤ) (by linarith) (by linarith),
      mem_apInterval_iff a b 21 ((r % 21 : ℕ) : ℤ) (by linarith) (by linarith)]
  constructor
  · rintro ⟨hp, ha_lt, hb_le, hmod42⟩
    refine ⟨hp, ha_lt, hb_le, ?_⟩
    have hnat42 : p % 42 = r := by
      have heq : p % 42 = r % 42 := by exact_mod_cast hmod42
      rwa [Nat.mod_eq_of_lt hr] at heq
    have hnat21 : p % 21 = (r % 21) % 21 := by omega
    exact_mod_cast hnat21
  · rintro ⟨hp, ha_lt, hb_le, hmod21⟩
    refine ⟨hp, ha_lt, hb_le, ?_⟩
    have hp_gt2 : 2 < p := by
      have : (2 : ℝ) < (p : ℝ) := lt_of_le_of_lt ha ha_lt
      exact_mod_cast this
    have hp_odd : p % 2 = 1 := by
      by_contra h2
      have hdvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
      rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega
    have hnat21 : p % 21 = r % 21 := by
      have heq : p % 21 = (r % 21) % 21 := by exact_mod_cast hmod21
      rwa [Nat.mod_eq_of_lt (Nat.mod_lt r (by decide))] at heq
    have hnat42 : p % 42 = r % 42 := by omega
    exact_mod_cast hnat42

/-- Section TL4: For any reduced residue `r < 42` coprime to `42` and `2 ≤ a ≤ b`,
    the theta increment modulo `42` equals the theta increment modulo `21`. -/
theorem thetaAP_forty_two_increment_eq_twenty_one {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    {r : ℕ} (hr : r < 42) (hcop : Nat.Coprime r 42) :
    thetaAP b 42 (r : ℤ) - thetaAP a 42 (r : ℤ) =
      thetaAP b 21 ((r % 21 : ℕ) : ℤ) - thetaAP a 21 ((r % 21 : ℕ) : ℤ) := by
  rw [thetaAP_sub_eq_interval_sum a b 42 (r : ℤ) hab,
      thetaAP_sub_eq_interval_sum a b 21 ((r % 21 : ℕ) : ℤ) hab,
      apInterval_forty_two_eq_twenty_one ha hab hr hcop]

end

end Sude
