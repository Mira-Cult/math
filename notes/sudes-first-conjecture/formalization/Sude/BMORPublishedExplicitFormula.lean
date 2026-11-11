import Sude.BMORExplicitFormulaImports
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Verbatim Published BMOR (2018) Explicit Formula and Zero-Sum Derivation

This module encodes the **verbatim published primary statements** of
Bennett–Martin–O'Bryant–Rechnitzer (2018), *Explicit bounds for primes in arithmetic
progressions*, Illinois J. Math. 62 (2018), 427–532 (`arXiv:1802.00085v3`), using
Mathlib's `ArithmeticFunction.vonMangoldt`, `DirichletCharacter ℂ q`,
`DirichletCharacter.LFunction`, `DirichletCharacter.conductor`, and `analyticOrderNatAt`:

1. **Proposition 2.1, equations `(2.3)`–`(2.7)` (printed pp. 438–439)**:
   The smoothed explicit formula for `ψ(x; q, a)` in terms of `U_{q,m}(x; δ, H)`,
   `V_{q,m}(x; δ, H)`, and `W_q(x)`.
2. **Proposition 2.5, equation `(2.10)` (printed p. 441)**:
   Two-sided critical-strip zero-count bound for `N(T, χ)` retaining the actual
   primitive conductor `χ.conductor` (`C₁ = 0.399`, `C₂ = 5.338`).
3. **Definition 2.6 & Proposition 2.7 (printed p. 441)**:
   Critical-line verification `GRH(H₀(d))` up to `30610046000` for `d = 1` and
   `10^8 / d` for `1 < d ≤ 100000`.
4. **Definition 3.1 (p. 451) & Proposition 4.34 (printed pp. 478–479)**:
   Unconditional zero-free region with `R = 5.6 = 28/5` for `q ≤ 100000`.

From these four verbatim published inputs alone (plus `RSThetaUpper`, Rosser–Schoenfeld
(1962) Theorem 4 `(3.15)`, p. 70), we **prove** in Lean:
- `chebyshevPsiAP_eq_psiAP`: Equivalence between von Mangoldt `ψ(x; q, a)` and `psiAP`.
- `bmorZeroMult_eq_primitive` & `bmorZeroMult_one_sub_star`: Imprimitive critical-strip
  invariance (`Z(χ) = Z(χ*)`) and functional-equation multiplicity symmetry (`ρ ↔ 1 - ρ̄`).
- `bmorU_term_summable`: Absolute convergence (`Summable`) of every high-zero series in
  `U_{q,m}(x; δ, H)` for `m ≥ 1`.
- `bmorExplicitFormulaImports_of_published`: Complete kernel-verified proof of
  `BMORExplicitFormulaImports` (`BMORSmoothedPsiSmallModuli`, `BMORSmoothedPsiModTwo`,
  and `RSThetaUpper`), eliminating all manuscript-level Stieltjes shortcuts from the
  analytic trust boundary.
-/

set_option autoImplicit false

namespace Sude

noncomputable section

open scoped BigOperators Interval
open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 8000000

/-! ## 1. Standard Chebyshev `ψ(x; q, a)` via `ArithmeticFunction.vonMangoldt` -/

/-- Standard Chebyshev function in an arithmetic progression (BMOR p. 430):
    `ψ(x; q, a) = ∑_{1 ≤ n ≤ x, n ≡ a (mod q)} Λ(n)`. -/
def chebyshevPsiAP (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    if ((n : ℤ) % (q : ℤ) = a % (q : ℤ)) then ArithmeticFunction.vonMangoldt n else 0

/-- Equivalence between the von Mangoldt definition `chebyshevPsiAP` and `psiAP` for `x ≥ 2`. -/
theorem chebyshevPsiAP_eq_psiAP {x : ℝ} (hx : 2 ≤ x) (q : ℕ) (a : ℤ) :
    chebyshevPsiAP x q a = psiAP x q a := by
  classical
  have hx0 : 0 ≤ x := by linarith
  let f : ℕ → ℝ := fun n =>
    if ((n : ℤ) % (q : ℤ) = a % (q : ℤ)) then Real.log (Nat.minFac n) else 0
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hlhs : chebyshevPsiAP x q a = ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter IsPrimePow, f n := by
    rw [chebyshevPsiAP, hIcc, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ArithmeticFunction.vonMangoldt_apply]
    dsimp [f]
    split_ifs <;> rfl
  rw [hlhs, Chebyshev.sum_PrimePow_eq_sum_sum f hx0]
  have hterm : ∀ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
      (∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime, f (p ^ k)) =
        thetaPowerAP x k q a := by
    intro k hk
    have hk_ne : k ≠ 0 := by
      have hk1 := (Finset.mem_Icc.mp hk).1
      omega
    rw [thetaPowerAP, Finset.sum_filter]
    have hdom : Finset.Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ ⊆ Finset.range (⌊x ^ (1 / (k : ℝ))⌋₊ + 1) := by
      intro p hp
      rw [Finset.mem_Ioc] at hp
      rw [Finset.mem_range]
      omega
    have hzero : ∀ p ∈ Finset.range (⌊x ^ (1 / (k : ℝ))⌋₊ + 1),
        p ∉ Finset.Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ →
        (if Nat.Prime p ∧ ((p ^ k : ℕ) : ℤ) % (q : ℤ) = a % (q : ℤ) then Real.log (p : ℝ) else 0) = 0 := by
      intro p hp hnot
      rw [Finset.mem_range] at hp
      rw [Finset.mem_Ioc] at hnot
      have hp0 : p = 0 := by omega
      subst hp0
      simp [Nat.not_prime_zero]
    rw [← Finset.sum_subset hdom hzero]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : Nat.Prime p
    · simp only [f, hp, true_and, if_true, hp.pow_minFac hk_ne]
    · simp [hp]
  rw [Finset.sum_congr rfl hterm]
  have hN1 : 1 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    rw [Nat.one_le_floor_iff, one_le_div (Real.log_pos (by norm_num))]
    exact Real.log_le_log (by norm_num) hx
  have hsplit : Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ =
      insert 1 (Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hk1 : thetaPowerAP x 1 q a = thetaAP x q a := by
    unfold thetaPowerAP thetaAP
    simp
  rw [hk1, psiAP, psiProperAP]

/-! ## 2. Critical-Strip Zeros, Multiplicity, Finiteness, and Symmetry -/

/-- BMOR Section 2.1 (p. 438): non-trivial critical-strip zero `ρ = β + i γ` of `L(s, χ)`
    with `0 < β < 1` (excluding `β = 0` so imprimitive Euler factors do not vanish). -/
def bmorIsCriticalZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0

/-- Multiplicity of `ρ` in BMOR's critical-strip zero multiset `Z(χ)` (`0` outside `0 < Re ρ < 1`). -/
def bmorZeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  if 0 < ρ.re ∧ ρ.re < 1 then analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ else 0

/-- Underlying set of critical-strip zeros of `L(s, χ)` up to ordinate height `T`. -/
def bmorZerosUpTo {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Set ℂ :=
  {ρ : ℂ | bmorIsCriticalZero χ ρ ∧ |ρ.im| ≤ T}

/-- Every Dirichlet character value in `ℂ` has norm at most `1`. -/
private theorem norm_dirichletCharacter_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hpow : (χ (u : ZMod q)) ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← map_pow]
      have hu : u ^ Fintype.card (ZMod q)ˣ = 1 := pow_card_eq_one
      rw [← Units.val_pow_eq_pow_val, hu]
      exact χ.map_one
    have hnorm_pow : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← norm_pow, hpow, norm_one]
    have hcard_ne : Fintype.card (ZMod q)ˣ ≠ 0 := Fintype.card_ne_zero
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hcard_ne).mp hnorm_pow).le
  · rw [χ.map_nonunit ha, norm_zero]
    exact zero_le_one

/-- Complex conjugate of a Dirichlet character value in `ℂ` equals the inverse character value. -/
private theorem star_dirichletCharacter_apply {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    star (χ a) = χ⁻¹ a := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hpow : (χ (u : ZMod q)) ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← map_pow]
      have hu : u ^ Fintype.card (ZMod q)ˣ = 1 := pow_card_eq_one
      rw [← Units.val_pow_eq_pow_val, hu]
      exact χ.map_one
    have hnorm : ‖χ (u : ZMod q)‖ = 1 := by
      have hnorm_pow : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
        rw [← norm_pow, hpow, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).mp hnorm_pow
    have hne : χ (u : ZMod q) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hnorm; norm_num at hnorm
    apply mul_right_cancel₀ hne
    have h1 : star (χ (u : ZMod q)) * χ (u : ZMod q) = 1 := by
      have hstar : star (χ (u : ZMod q)) = (starRingEnd ℂ) (χ (u : ZMod q)) := by simp
      rw [hstar, RCLike.conj_mul, hnorm]
      norm_num
    have h2 : χ⁻¹ (u : ZMod q) * χ (u : ZMod q) = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply u.isUnit]
    exact h1.trans h2.symm
  · rw [χ.map_nonunit ha, χ⁻¹.map_nonunit ha, star_zero]

/-- An Euler factor `1 - ψ p * p^(-s)` is nonzero for `Re s > 0` and prime `p`. -/
private theorem euler_factor_ne_zero {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d)
    {p : ℕ} (hp : Nat.Prime p) {s : ℂ} (hs : 0 < s.re) :
    1 - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h0
  have heq : ψ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h0).symm
  have hnorm1 : ‖ψ p * (p : ℂ) ^ (-s)‖ = 1 := by rw [heq, norm_one]
  rw [norm_mul] at hnorm1
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hcpow : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-s)
  have hrpow_lt : (p : ℝ) ^ (-s.re) < 1 := by
    rw [← Real.rpow_zero (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp_gt1 (neg_lt_zero.mpr hs)
  have hψ : ‖ψ p‖ ≤ 1 := norm_dirichletCharacter_le_one ψ p
  have hlt : ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hcpow]
    nlinarith [norm_nonneg (ψ p), Real.rpow_pos_of_pos hp_pos (-s.re)]
  linarith

/-- Analyticity of `L(s, χ)` away from `s = 1`. -/
private theorem analyticOnNhd_LFunction_compl_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_compl_singleton
  exact (DirichletCharacter.differentiableAt_LFunction χ s (.inl hs)).differentiableWithinAt

private theorem analyticAt_LFunction_of_ne_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (DirichletCharacter.LFunction χ) s :=
  analyticOnNhd_LFunction_compl_one χ s hs

/-- `L(s, χ)` never vanishes identically near any `s ≠ 1`. -/
private theorem analyticOrderAt_LFunction_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) 1).isPreconnected
  have h2_mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have h0 := (analyticOnNhd_LFunction_compl_one χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hpc hs htop h2_mem
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num) h0

/-- In the critical strip, `0 < bmorZeroMult χ ρ` iff `ρ` is a critical-strip zero of `L(s, χ)`. -/
theorem bmorZeroMult_pos_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    0 < bmorZeroMult χ ρ ↔ bmorIsCriticalZero χ ρ := by
  unfold bmorZeroMult bmorIsCriticalZero
  split_ifs with hstrip
  · have hne1 : ρ ≠ 1 := by
      intro h1; subst h1; simp at hstrip
    have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
      analyticAt_LFunction_of_ne_one χ hne1
    have hntop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
      analyticOrderAt_LFunction_ne_top χ hne1
    constructor
    · intro hpos
      refine ⟨hstrip.1, hstrip.2, ?_⟩
      by_contra hnz
      have hz0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ = 0 :=
        analyticOrderAt_eq_zero.mpr (.inr hnz)
      simp [analyticOrderNatAt, hz0] at hpos
    · rintro ⟨_, _, hz⟩
      by_contra hnotpos
      have hnat0 : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 0 := by omega
      have hord0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ = 0 := by
        rw [← Nat.cast_analyticOrderNatAt hntop, hnat0]; rfl
      rcases analyticOrderAt_eq_zero.mp hord0 with hna | hnz
      · exact hna han
      · exact hnz hz
  · exact ⟨fun h => absurd h (lt_irrefl 0), fun ⟨h1, h2, _⟩ => False.elim (hstrip ⟨h1, h2⟩)⟩

theorem bmorZeroMult_eq_zero_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    bmorZeroMult χ ρ = 0 ↔ ¬ bmorIsCriticalZero χ ρ := by
  rw [← bmorZeroMult_pos_iff]
  omega

/-- Every critical-strip zero set up to bounded ordinate height `T` is finite. -/
theorem bmorFiniteZerosUpTo {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (bmorZerosUpTo χ T).Finite := by
  let R : ℝ := 1 + max T 0
  have hsub_ball : bmorZerosUpTo χ T ⊆ Metric.closedBall (0 : ℂ) R := by
    intro ρ hρ
    rcases hρ with ⟨⟨hre0, hre1, _⟩, him⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    have habs_re : |ρ.re| ≤ 1 := abs_le.mpr ⟨by linarith, hre1.le⟩
    have habs_im : |ρ.im| ≤ max T 0 := him.trans (le_max_left T 0)
    dsimp [R]
    linarith
  by_cases hχ : χ = 1
  · subst hχ
    have hsub : bmorZerosUpTo (1 : DirichletCharacter ℂ q) T ⊆
        Metric.closedBall (0 : ℂ) R ∩ riemannZetaZeros := by
      intro ρ hρ
      refine ⟨hsub_ball hρ, ?_⟩
      rcases hρ with ⟨⟨hre0, hre1, hL0⟩, _⟩
      have hne1 : ρ ≠ 1 := by intro h1; subst h1; simp at hre1
      have htriv := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hne1
      change DirichletCharacter.LFunctionTrivChar q ρ = 0 at hL0
      rw [htriv] at hL0
      have hprod_ne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-ρ))) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro p hp
        simpa [MulChar.one_apply (isUnit_of_subsingleton _)] using
          euler_factor_ne_zero (1 : DirichletCharacter ℂ 1) (Nat.prime_of_mem_primeFactors hp) hre0
      exact (mul_eq_zero.mp hL0).resolve_left hprod_ne
    exact (isCompact_closedBall (0 : ℂ) R).inter_riemannZetaZeros_finite.subset hsub
  · have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
    have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by norm_num)
    have hcodisc : ((DirichletCharacter.LFunction χ) ⁻¹' {0})ᶜ ∈ Filter.codiscrete ℂ := by
      rw [Filter.codiscrete]
      exact han.preimage_zero_mem_codiscreteWithin (x := 2) h2 (Set.mem_univ _) isConnected_univ
    obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcodisc
    have hfin : (Metric.closedBall (0 : ℂ) R ∩ ((DirichletCharacter.LFunction χ) ⁻¹' {0})).Finite :=
      ((isCompact_closedBall (0 : ℂ) R).inter_right hclosed).finite
        (hdisc.mono Set.inter_subset_right)
    refine hfin.subset fun ρ hρ => ⟨hsub_ball hρ, ?_⟩
    exact hρ.1.2.2

/-- Finite set of critical-strip zeros of `L(s, χ)` with `|Im ρ| ≤ T`. -/
def bmorCriticalZerosUpTo {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Finset ℂ :=
  (bmorFiniteZerosUpTo χ T).toFinset

@[simp]
theorem mem_bmorCriticalZerosUpTo {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) (ρ : ℂ) :
    ρ ∈ bmorCriticalZerosUpTo χ T ↔ bmorIsCriticalZero χ ρ ∧ |ρ.im| ≤ T := by
  simp [bmorCriticalZerosUpTo, bmorZerosUpTo]

/-- BMOR Definition 2.2 (p. 440): `N(T, χ)` counts critical-strip zeros `ρ ∈ Z(χ)`
    with `|Im ρ| ≤ T`, counted with multiplicity. -/
def bmorZeroCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  ∑ ρ ∈ bmorCriticalZerosUpTo χ T, bmorZeroMult χ ρ

/-- BMOR Section 2.1 (p. 438): `χ` satisfies `GRH(H)` iff every `ρ ∈ Z(χ)` with
    `|Im ρ| ≤ H` has `Re ρ = 1/2`. -/
def bmorSatisfiesGRH {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H : ℝ) : Prop :=
  ∀ ρ : ℂ, bmorIsCriticalZero χ ρ → |ρ.im| ≤ H → ρ.re = 1 / 2

/-- Imprimitive invariance `Z(χ) = Z(χ*)` (BMOR Section 2.1, p. 438):
    critical-strip zero multiplicities of `χ` agree with those of `χ.primitiveCharacter`. -/
theorem bmorZeroMult_eq_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    bmorZeroMult χ ρ =
      @bmorZeroMult χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter ρ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  unfold bmorZeroMult
  split_ifs with hstrip
  · let ψ := χ.primitiveCharacter
    let P : ℂ → ℂ := fun w => ∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-w))
    have hne1 : ρ ≠ 1 := by intro h1; subst h1; simp at hstrip
    have heq_nhds : DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ]
        fun w => DirichletCharacter.LFunction ψ w * P w := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hne1] with w hw
      conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
      exact DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level ψ (.inr hw)
    have hanψ : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) ρ :=
      analyticAt_LFunction_of_ne_one ψ hne1
    have hanP : AnalyticAt ℂ P ρ := by
      refine DifferentiableOn.analyticAt (s := Set.univ) (fun w _ => ?_) univ_mem
      refine DifferentiableAt.differentiableWithinAt ?_
      dsimp [P]
      refine DifferentiableAt.fun_finsetProd fun p hp => ?_
      have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact differentiableAt_const _ |>.sub
        ((differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow (.inl hp_ne)))
    have hP_ne : P ρ ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp =>
        euler_factor_ne_zero ψ (Nat.prime_of_mem_primeFactors hp) hstrip.1
    have hordP : analyticOrderAt P ρ = 0 := analyticOrderAt_eq_zero.mpr (.inr hP_ne)
    have hord : analyticOrderAt (DirichletCharacter.LFunction χ) ρ =
        analyticOrderAt (DirichletCharacter.LFunction ψ) ρ := by
      rw [analyticOrderAt_congr heq_nhds]
      change analyticOrderAt (DirichletCharacter.LFunction ψ * P) ρ = _
      rw [analyticOrderAt_mul hanψ hanP, hordP, add_zero]
    dsimp [ψ] at hord
    simp [analyticOrderNatAt, hord]
  · rfl

theorem bmorIsCriticalZero_iff_primitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    bmorIsCriticalZero χ ρ ↔
      @bmorIsCriticalZero χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter ρ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [← bmorZeroMult_pos_iff, ← bmorZeroMult_pos_iff, bmorZeroMult_eq_primitive]

theorem bmorSatisfiesGRH_of_primitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {H : ℝ}
    (hprim : @bmorSatisfiesGRH χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter H) :
    bmorSatisfiesGRH χ H := by
  intro ρ hρ him
  exact hprim ρ ((bmorIsCriticalZero_iff_primitive χ ρ).mp hρ) him

/-- Schwarz reflection for `AnalyticAt` under `w ↦ star (g (star w))`. -/
private theorem analyticAt_conj_conj {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (fun w => star (g (star w))) (star z₀) := by
  have hev : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z :=
    hg.eventually_analyticAt.mono fun _ hz => hz.differentiableAt
  let S : Set ℂ := {w : ℂ | DifferentiableAt ℂ g (star w)}
  have hS_nhds : S ∈ 𝓝 (star z₀) := by
    have htend : Tendsto (star : ℂ → ℂ) (𝓝 (star z₀)) (𝓝 z₀) := by
      simpa [star_star] using (continuous_star.continuousAt (x := star z₀)).tendsto
    exact htend hev
  refine DifferentiableOn.analyticAt (s := S) (fun w hw => ?_) hS_nhds
  have hd : DifferentiableAt ℂ (fun u => star (g (star u))) w := by
    have h1 : DifferentiableAt ℂ g ((starRingEnd ℂ) w) := by simpa [S] using hw
    have h2 : DifferentiableAt ℂ (star ∘ g ∘ (starRingEnd ℂ)) w :=
      differentiableAt_star_conj_iff.mpr h1
    have hfun : (fun u => star (g (star u))) = star ∘ g ∘ (starRingEnd ℂ) := by
      ext u; simp [Function.comp_apply]
    rw [hfun]
    exact h2
  exact hd.differentiableWithinAt

/-- Schwarz reflection preserves `analyticOrderAt`. -/
private theorem analyticOrderAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hntop : analyticOrderAt f z₀ ≠ ⊤) :
    analyticOrderAt (fun w => star (f (star w))) (star z₀) = analyticOrderAt f z₀ := by
  set n := analyticOrderNatAt f z₀
  have hord : analyticOrderAt f z₀ = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt hntop).symm
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (hf.analyticOrderAt_eq_natCast).mp hord
  have hf_conj_an : AnalyticAt ℂ (fun w => star (f (star w))) (star z₀) :=
    analyticAt_conj_conj hf
  rw [hord, hf_conj_an.analyticOrderAt_eq_natCast]
  refine ⟨fun w => star (g (star w)), analyticAt_conj_conj hg_an, ?_, ?_⟩
  · simp [hg_ne]
  · have htend : Tendsto (star : ℂ → ℂ) (𝓝 (star z₀)) (𝓝 z₀) := by
      simpa [star_star] using (continuous_star.continuousAt (x := star z₀)).tendsto
    filter_upwards [htend hg_eq] with w hw
    simp only [smul_eq_mul] at hw ⊢
    have h1 := congrArg (star : ℂ → ℂ) hw
    simpa [star_mul, star_pow, star_sub, star_star, mul_comm] using h1

/-- Schwarz reflection identity `L(s, χ⁻¹) = conj (L(conj s, χ))` for `s ≠ 1`. -/
private theorem LFunction_inv_eq_star_LFunction_star {d : ℕ} [NeZero d]
    (ψ : DirichletCharacter ℂ d) {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction ψ⁻¹ s = star (DirichletCharacter.LFunction ψ (star s)) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) 1).isPreconnected
  have h2_mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := DirichletCharacter.LFunction ψ⁻¹)
    (g := fun w => star (DirichletCharacter.LFunction ψ (star w)))
    (analyticOnNhd_LFunction_compl_one ψ⁻¹) ?_ hpc h2_mem ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_compl_singleton
    have hw_star : star w ≠ (1 : ℂ) := by
      intro h1
      apply hw
      simpa using congrArg (star : ℂ → ℂ) h1
    have hd := DirichletCharacter.differentiableAt_LFunction ψ (star w) (.inl hw_star)
    have hd_conj : DifferentiableAt ℂ (fun u => star (DirichletCharacter.LFunction ψ (star u))) w := by
      have h1 : DifferentiableAt ℂ (DirichletCharacter.LFunction ψ) ((starRingEnd ℂ) w) := by
        simpa using hd
      have h2 : DifferentiableAt ℂ (star ∘ DirichletCharacter.LFunction ψ ∘ (starRingEnd ℂ)) w :=
        differentiableAt_star_conj_iff.mpr h1
      have hfun : (fun u => star (DirichletCharacter.LFunction ψ (star u))) =
          star ∘ DirichletCharacter.LFunction ψ ∘ (starRingEnd ℂ) := by
        ext u; simp [Function.comp_apply]
      rw [hfun]
      exact h2
    exact hd_conj.differentiableWithinAt
  · have hopen : {t : ℂ | 1 < t.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with t (ht : 1 < t.re)
    have ht_star : 1 < (star t).re := by simpa using ht
    rw [DirichletCharacter.LFunction_eq_LSeries ψ⁻¹ ht,
        DirichletCharacter.LFunction_eq_LSeries ψ ht_star]
    unfold LSeries
    have hstar_eq : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => by simp
    rw [hstar_eq, Complex.conj_tsum]
    congr 1
    ext n
    unfold LSeries.term
    split_ifs with hn0
    · simp
    · simp only [map_div₀]
      rw [← hstar_eq (ψ n), star_dirichletCharacter_apply ψ n]
      congr 1
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      have harg : ((n : ℝ) : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hn_pos.le]
        exact Real.pi_ne_zero.symm
      have hc := Complex.cpow_conj ((n : ℝ) : ℂ) (star t) harg
      simpa using hc

/-- Nonvanishing of `rootNumber ψ` for primitive `ψ` (deduced directly from the functional
    equation evaluated at `s = -1`, where `1 - s = 2` is in the region of nonvanishing). -/
private theorem rootNumber_ne_zero_of_isPrimitive {d : ℕ} [NeZero d]
    {ψ : DirichletCharacter ℂ d} (hψ : ψ.IsPrimitive) :
    DirichletCharacter.rootNumber ψ ≠ 0 := by
  have hL2 : DirichletCharacter.LFunction ψ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (.inr (by norm_num)) (by norm_num)
  have hcomp2 : DirichletCharacter.completedLFunction ψ 2 ≠ 0 := by
    intro h0
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ 2 (.inl (by norm_num)),
        h0, zero_div] at hL2
    exact hL2 rfl
  have hfe := hψ.completedLFunction_one_sub (-1 : ℂ)
  have h1sub : (1 : ℂ) - (-1 : ℂ) = 2 := by ring
  rw [h1sub] at hfe
  intro hr0
  rw [hr0, mul_zero, zero_mul] at hfe
  exact hcomp2 hfe

/-- Functional-equation symmetry of critical-strip zero multiplicity:
    `bmorZeroMult χ (1 - star ρ) = bmorZeroMult χ ρ` (BMOR Section 2.1, p. 438). -/
theorem bmorZeroMult_one_sub_star {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    bmorZeroMult χ (1 - star ρ) = bmorZeroMult χ ρ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [bmorZeroMult_eq_primitive χ (1 - star ρ), bmorZeroMult_eq_primitive χ ρ]
  let ψ := χ.primitiveCharacter
  have hψ : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hstrip_iff : (0 < (1 - star ρ).re ∧ (1 - star ρ).re < 1) ↔ (0 < ρ.re ∧ ρ.re < 1) := by
    have hre : (1 - star ρ).re = 1 - ρ.re := by simp
    rw [hre]
    constructor <;> intro h <;> constructor <;> linarith
  unfold bmorZeroMult
  by_cases hstrip : 0 < ρ.re ∧ ρ.re < 1
  · have hstrip' : 0 < (1 - star ρ).re ∧ (1 - star ρ).re < 1 := hstrip_iff.mpr hstrip
    rw [if_pos hstrip', if_pos hstrip]
    -- Helper: on `0 < z.re ∧ z.re < 1`, `LFunction` and `completedLFunction` have equal `analyticOrderAt`
    have hord_comp : ∀ (ξ : DirichletCharacter ℂ χ.conductor) {z : ℂ},
        0 < z.re → z.re < 1 →
        analyticOrderAt (DirichletCharacter.LFunction ξ) z =
          analyticOrderAt (DirichletCharacter.completedLFunction ξ) z := by
      intro ξ z hz0 hz1
      have hne0 : z ≠ 0 := by intro h0; subst h0; simp at hz0
      have hne1 : z ≠ 1 := by intro h1; subst h1; simp at hz1
      have heq : DirichletCharacter.LFunction ξ =ᶠ[𝓝 z]
          fun w => DirichletCharacter.completedLFunction ξ w *
            (DirichletCharacter.gammaFactor ξ w)⁻¹ := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hne0] with w hw
        rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ξ w (.inl hw), div_eq_mul_inv]
      have han_comp : AnalyticAt ℂ (DirichletCharacter.completedLFunction ξ) z := by
        have hopen : ({0}ᶜ ∩ {1}ᶜ : Set ℂ) ∈ 𝓝 z :=
          Filter.inter_mem (isOpen_compl_singleton.mem_nhds hne0) (isOpen_compl_singleton.mem_nhds hne1)
        refine DifferentiableOn.analyticAt (s := {0}ᶜ ∩ {1}ᶜ) (fun w hw => ?_) hopen
        exact (DirichletCharacter.differentiableAt_completedLFunction ξ w
          (.inl hw.1) (.inl hw.2)).differentiableWithinAt
      have han_gam : AnalyticAt ℂ (fun w => (DirichletCharacter.gammaFactor ξ w)⁻¹) z := by
        rcases ξ.even_or_odd with hev | hodd
        · have hfun : (fun w => (DirichletCharacter.gammaFactor ξ w)⁻¹) = fun w => (Gammaℝ w)⁻¹ := by
            ext w; rw [hev.gammaFactor_def]
          rw [hfun]
          exact Complex.differentiable_Gammaℝ_inv.analyticAt z
        · have hfun : (fun w => (DirichletCharacter.gammaFactor ξ w)⁻¹) =
              fun w => (Gammaℝ (w + 1))⁻¹ := by
            ext w; rw [hodd.gammaFactor_def]
          rw [hfun]
          exact (Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)).analyticAt z
      have hgam_ne : (DirichletCharacter.gammaFactor ξ z)⁻¹ ≠ 0 := by
        apply inv_ne_zero
        rcases ξ.even_or_odd with hev | hodd
        · rw [hev.gammaFactor_def]
          exact Complex.Gammaℝ_ne_zero_of_re_pos hz0
        · rw [hodd.gammaFactor_def]
          exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
      have hord_gam : analyticOrderAt (fun w : ℂ => (DirichletCharacter.gammaFactor ξ w)⁻¹) z = 0 :=
        analyticOrderAt_eq_zero.mpr (.inr hgam_ne)
      rw [analyticOrderAt_congr heq]
      change analyticOrderAt
        (DirichletCharacter.completedLFunction ξ * fun w : ℂ => (DirichletCharacter.gammaFactor ξ w)⁻¹) z = _
      rw [analyticOrderAt_mul han_comp han_gam, hord_gam, add_zero]
    -- Apply at `1 - star ρ` and `star ρ`
    have h1 := hord_comp ψ hstrip'.1 hstrip'.2
    have hstar_re0 : 0 < (star ρ).re := by simpa using hstrip.1
    have hstar_re1 : (star ρ).re < 1 := by simpa using hstrip.2
    have h2 := hord_comp ψ⁻¹ hstar_re0 hstar_re1
    -- Relate `completedLFunction ψ` at `1 - star ρ` to `completedLFunction ψ⁻¹` at `star ρ`
    have hcomp_one_sub : analyticOrderAt (DirichletCharacter.completedLFunction ψ) (1 - star ρ) =
        analyticOrderAt (fun w => DirichletCharacter.completedLFunction ψ (1 - w)) (star ρ) := by
      have hg_an : AnalyticAt ℂ (fun w : ℂ => 1 - w) (star ρ) :=
        analyticAt_const.sub analyticAt_id
      have hg_deriv : deriv (fun w : ℂ => 1 - w) (star ρ) ≠ 0 := by
        rw [deriv_const_sub_id]
        norm_num
      exact (analyticOrderAt_comp_of_deriv_ne_zero hg_an hg_deriv).symm
    have hfe_fun : (fun w => DirichletCharacter.completedLFunction ψ (1 - w)) =
        fun w => ((χ.conductor : ℂ) ^ (w - 1 / 2) * DirichletCharacter.rootNumber ψ) *
          DirichletCharacter.completedLFunction ψ⁻¹ w := by
      ext w; exact hψ.completedLFunction_one_sub w
    have hpref_an : AnalyticAt ℂ
        (fun w : ℂ => (χ.conductor : ℂ) ^ (w - 1 / 2) * DirichletCharacter.rootNumber ψ) (star ρ) := by
      have hd_ne : (χ.conductor : ℂ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
      refine DifferentiableOn.analyticAt (s := Set.univ) (fun w _ => ?_) univ_mem
      refine DifferentiableAt.differentiableWithinAt ?_
      exact (((differentiableAt_id.sub_const (1 / 2 : ℂ)).const_cpow (.inl hd_ne)).mul
        (differentiableAt_const _))
    have hpref_ne : (χ.conductor : ℂ) ^ (star ρ - 1 / 2) * DirichletCharacter.rootNumber ψ ≠ 0 := by
      apply mul_ne_zero
      · have hd_ne : (χ.conductor : ℂ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
        rw [Complex.cpow_def_of_ne_zero hd_ne]
        exact Complex.exp_ne_zero _
      · exact rootNumber_ne_zero_of_isPrimitive hψ
    have han_comp_inv : AnalyticAt ℂ (DirichletCharacter.completedLFunction ψ⁻¹) (star ρ) := by
      have hne0 : star ρ ≠ 0 := by intro h0; rw [h0] at hstar_re0; simp at hstar_re0
      have hne1 : star ρ ≠ 1 := by intro h1; rw [h1] at hstar_re1; simp at hstar_re1
      have hopen : ({0}ᶜ ∩ {1}ᶜ : Set ℂ) ∈ 𝓝 (star ρ) :=
        Filter.inter_mem (isOpen_compl_singleton.mem_nhds hne0) (isOpen_compl_singleton.mem_nhds hne1)
      refine DifferentiableOn.analyticAt (s := {0}ᶜ ∩ {1}ᶜ) (fun w hw => ?_) hopen
      exact (DirichletCharacter.differentiableAt_completedLFunction ψ⁻¹ w
        (.inl hw.1) (.inl hw.2)).differentiableWithinAt
    have hfe_ord : analyticOrderAt (DirichletCharacter.completedLFunction ψ) (1 - star ρ) =
        analyticOrderAt (DirichletCharacter.completedLFunction ψ⁻¹) (star ρ) := by
      have hord_pref : analyticOrderAt
          (fun w : ℂ => (χ.conductor : ℂ) ^ (w - 1 / 2) * DirichletCharacter.rootNumber ψ) (star ρ) = 0 :=
        analyticOrderAt_eq_zero.mpr (.inr hpref_ne)
      rw [hcomp_one_sub, hfe_fun]
      change analyticOrderAt
        ((fun w : ℂ => (χ.conductor : ℂ) ^ (w - 1 / 2) * DirichletCharacter.rootNumber ψ) *
          DirichletCharacter.completedLFunction ψ⁻¹) (star ρ) = _
      rw [analyticOrderAt_mul hpref_an han_comp_inv, hord_pref, zero_add]
    -- Relate `LFunction ψ⁻¹` at `star ρ` to `LFunction ψ` at `ρ` via Schwarz reflection
    have hne1_ρ : ρ ≠ 1 := by intro h1; subst h1; simp at hstrip
    have hne1_star : star ρ ≠ 1 := by intro h1; rw [h1] at hstar_re1; simp at hstar_re1
    have hconj_nhds : DirichletCharacter.LFunction ψ⁻¹ =ᶠ[𝓝 (star ρ)]
        fun w => star (DirichletCharacter.LFunction ψ (star w)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hne1_star] with w hw
      exact LFunction_inv_eq_star_LFunction_star ψ hw
    have hconj_ord : analyticOrderAt (DirichletCharacter.LFunction ψ⁻¹) (star ρ) =
        analyticOrderAt (DirichletCharacter.LFunction ψ) ρ := by
      rw [analyticOrderAt_congr hconj_nhds]
      exact analyticOrderAt_conj_conj (analyticAt_LFunction_of_ne_one ψ hne1_ρ)
        (analyticOrderAt_LFunction_ne_top ψ hne1_ρ)
    have htotal : analyticOrderAt (DirichletCharacter.LFunction ψ) (1 - star ρ) =
        analyticOrderAt (DirichletCharacter.LFunction ψ) ρ := by
      rw [h1, hfe_ord, ← h2, hconj_ord]
    unfold analyticOrderNatAt
    change (analyticOrderAt (DirichletCharacter.LFunction ψ) (1 - star ρ)).toNat =
      (analyticOrderAt (DirichletCharacter.LFunction ψ) ρ).toNat
    rw [htotal]
  · have hstrip' : ¬ (0 < (1 - star ρ).re ∧ (1 - star ρ).re < 1) :=
      fun h => hstrip (hstrip_iff.mp h)
    rw [if_neg hstrip', if_neg hstrip]

/-! ## 3. Verbatim Published BMOR (2018) Propositions 2.1, 2.5, 2.7, and 4.34 -/

/-- Summand inside `U_{q,m}(x; δ, H)` for character `χ` and zero `ρ` (BMOR `(2.5)`, p. 439). -/
def bmorUTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) (x H : ℝ) (ρ : ℂ) : ℝ :=
  if H < |ρ.im| then
    (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ∏ j ∈ Finset.range (m + 1), ‖ρ + (j : ℂ)‖)
  else 0

/-- BMOR Proposition 2.1, equation `(2.5)` (p. 439):
    `U_{q,m}(x; δ, H) = A_m(δ) ∑_{χ mod q} ∑_{ρ ∈ Z(χ), |γ| > H} x^{β-1} / |ρ(ρ+1)⋯(ρ+m)|`. -/
def bmorU (q : ℕ) [NeZero q] (m : ℕ) (x δ H : ℝ) : ℝ :=
  bmorSmoothFactor m δ * ∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, bmorUTerm χ m x H ρ

/-- BMOR Proposition 2.1, equation `(2.6)` (p. 439):
    `V_{q,m}(x; δ, H) = (1 + m δ / 2) ∑_{χ mod q} ∑_{ρ ∈ Z(χ), |γ| ≤ H} x^{β-1} / |ρ|`. -/
def bmorV (q : ℕ) [NeZero q] (m : ℕ) (x δ H : ℝ) : ℝ :=
  (1 + (m : ℝ) * δ / 2) * ∑ χ : DirichletCharacter ℂ q,
    ∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖)

/-- BMOR Proposition 2.1, equation `(2.7)` (p. 439, `13.4 = 67 / 5`):
    `W_q(x) = (φ(q) / x) * ((1/2 + ∑_{p ∣ q} 1/(p-1)) log x + 4 log q + 67/5)`. -/
def bmorW (q : ℕ) (x : ℝ) : ℝ :=
  ((Nat.totient q : ℝ) / x) *
    ((1 / 2 + ∑ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1)) * Real.log x +
      4 * Real.log (q : ℝ) + 67 / 5)

/-- **BMOR (2018) Proposition 2.1, equation `(2.3)` (printed pp. 438–439)**, verbatim. -/
def BMORProp2_1 : Prop :=
  ∀ (q : ℕ) [NeZero q] (a : ℤ) (m : ℕ) (x δ H : ℝ),
    Nat.Coprime q a.natAbs →
    2 < x → 1 ≤ H → 1 ≤ m →
    0 < δ → δ < (x - 2) / ((m : ℝ) * x) →
    (∀ χ : DirichletCharacter ℂ q, bmorSatisfiesGRH χ 1) →
    ((Nat.totient q : ℝ) / x) * |chebyshevPsiAP x q a - x / (Nat.totient q : ℝ)| <
      bmorU q m x δ H + (m : ℝ) * δ / 2 + bmorV q m x δ H + bmorW q x

/-- **BMOR (2018) Proposition 2.5, equation `(2.10)` (printed p. 441)**, verbatim:
    two-sided bound for `N(T, χ)` retaining primitive conductor `d = χ.conductor`. -/
def BMORProp2_5 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ),
    1 ≤ T →
    |(bmorZeroCount χ T : ℝ) -
        (T / Real.pi) * Real.log (((χ.conductor : ℝ) * T) / (2 * Real.pi * Real.exp 1))| <
      bmorC1 * Real.log ((χ.conductor : ℝ) * T) + bmorC2

/-- **BMOR (2018) Definition 2.6 & Proposition 2.7 (printed p. 441)**, verbatim:
    every primitive character of conductor `d ≤ 100000` satisfies `GRH(bmorVerifiedHeight d)`. -/
def BMORProp2_7 : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
    χ.IsPrimitive → d ≤ 100000 →
    bmorSatisfiesGRH χ (bmorVerifiedHeight d)

/-- **BMOR (2018) Definition 3.1 (p. 451) & Proposition 4.34 (printed pp. 478–479)**, verbatim:
    for `1 ≤ q ≤ 100000`, every critical-strip zero of `L(s, χ)` either lies at height
    `|γ| ≤ 10^8 / q` with `β = 1/2` or at height `|γ| > 10^8 / q` with
    `β ≤ 1 - 1 / (5.6 * log(d * |γ|))`. -/
def BMORProp4_34 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    q ≤ 100000 →
    bmorIsCriticalZero χ ρ →
    (|ρ.im| ≤ (10 ^ 8 : ℝ) / (q : ℝ) ∧ ρ.re = 1 / 2) ∨
    ((10 ^ 8 : ℝ) / (q : ℝ) < |ρ.im| ∧
      ρ.re ≤ 1 - 1 / (bmorZeroFreeR * Real.log ((χ.conductor : ℝ) * |ρ.im|)))

/-- Bundled verbatim published analytic inputs from BMOR (2018). -/
structure BMORPublishedExplicitFormula : Prop where
  prop2_1 : BMORProp2_1
  prop2_5 : BMORProp2_5
  prop2_7 : BMORProp2_7
  prop4_34 : BMORProp4_34

/-! ## 4. Finite Stieltjes Summation Identity and Zero-Sum Bounds -/

/-- Exact indicator integral identity on `[a, b]` for `a ≤ t ≤ b`. -/
private theorem indicator_Ici_intervalIntegrable {a b t : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Set.Icc a b)) :
    IntervalIntegrable (Set.indicator (Set.Ici t) g) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hg.integrableOn_Icc.indicator measurableSet_Ici

private theorem integral_indicator_Ici_eq {a b t : ℝ} {g : ℝ → ℝ}
    (hat : a ≤ t) (htb : t ≤ b) (hg : ContinuousOn g (Set.Icc a b)) :
    (∫ u in a..b, Set.indicator (Set.Ici t) g u) = ∫ u in t..b, g u := by
  have hab : a ≤ b := hat.trans htb
  have hi1 : IntervalIntegrable (Set.indicator (Set.Ici t) g) volume a t :=
    indicator_Ici_intervalIntegrable hat (hg.mono (Set.Icc_subset_Icc_right htb))
  have hi2 : IntervalIntegrable (Set.indicator (Set.Ici t) g) volume t b :=
    indicator_Ici_intervalIntegrable htb (hg.mono (Set.Icc_subset_Icc_left hat))
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hleft : (∫ u in a..t, Set.indicator (Set.Ici t) g u) = 0 := by
    rw [intervalIntegral.integral_of_le hat]
    have hae : ∀ᵐ u ∂(volume.restrict (Set.Ioc a t)), Set.indicator (Set.Ici t) g u = 0 := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [Ioo_ae_eq_Ioc] with u hu hmem
      have hlt : u < t := (hu.mpr hmem).2
      exact Set.indicator_of_notMem (by simp [hlt.not_ge]) g
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_zero]
  have hright : (∫ u in t..b, Set.indicator (Set.Ici t) g u) = ∫ u in t..b, g u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le htb] at hu
    exact Set.indicator_of_mem (Set.mem_Ici.mpr hu.1.le) g
  rw [hleft, hright, zero_add]

/-- Decomposition of `bmorZeroCount` on `(a, u]` for `0 ≤ a ≤ u ≤ b`. -/
private theorem bmorZeroCount_Band_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b u : ℝ} (hau : a ≤ u) (hub : u ≤ b) :
    (∑ ρ ∈ (bmorCriticalZerosUpTo χ b).filter (fun ρ => a < |ρ.im|),
        if |ρ.im| ≤ u then (bmorZeroMult χ ρ : ℝ) else 0) =
      (bmorZeroCount χ u : ℝ) - (bmorZeroCount χ a : ℝ) := by
  classical
  have hsub_au : bmorCriticalZerosUpTo χ a ⊆ bmorCriticalZerosUpTo χ u := by
    intro ρ hρ
    rw [mem_bmorCriticalZerosUpTo] at hρ ⊢
    exact ⟨hρ.1, hρ.2.trans hau⟩
  have hdiff : ((bmorCriticalZerosUpTo χ b).filter (fun ρ => a < |ρ.im|)).filter (fun ρ => |ρ.im| ≤ u) =
      bmorCriticalZerosUpTo χ u \ bmorCriticalZerosUpTo χ a := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_sdiff, mem_bmorCriticalZerosUpTo]
    constructor
    · rintro ⟨⟨⟨hcrit, _⟩, hgt⟩, hle⟩
      exact ⟨⟨hcrit, hle⟩, fun h => not_le_of_gt hgt h.2⟩
    · rintro ⟨⟨hcrit, hle⟩, hnot⟩
      have hgt : a < |ρ.im| := by
        by_contra hle_a
        push Not at hle_a
        exact hnot ⟨hcrit, hle_a⟩
      exact ⟨⟨⟨hcrit, hle.trans hub⟩, hgt⟩, hle⟩
  rw [← Finset.sum_filter, hdiff]
  have hcast : (bmorZeroCount χ u : ℝ) = ∑ ρ ∈ bmorCriticalZerosUpTo χ u, (bmorZeroMult χ ρ : ℝ) := by
    simp [bmorZeroCount]
  have hcast_a : (bmorZeroCount χ a : ℝ) = ∑ ρ ∈ bmorCriticalZerosUpTo χ a, (bmorZeroMult χ ρ : ℝ) := by
    simp [bmorZeroCount]
  rw [hcast, hcast_a, ← Finset.sum_sdiff_eq_sub hsub_au]

/-- Exact finite Stieltjes summation formula for `bmorZeroCount χ` on `(a, b]`. -/
private theorem bmor_stieltjes_band_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hf_deriv : ∀ u ∈ Set.Icc a b, HasDerivAt f (f' u) u)
    (hf'_cont : ContinuousOn f' (Set.Icc a b)) :
    IntervalIntegrable (fun u => ((bmorZeroCount χ u : ℝ) - (bmorZeroCount χ a : ℝ)) * (-f' u))
      volume a b ∧
    (∑ ρ ∈ (bmorCriticalZerosUpTo χ b).filter (fun ρ => a < |ρ.im|),
        (bmorZeroMult χ ρ : ℝ) * f |ρ.im|) =
      ((bmorZeroCount χ b : ℝ) - (bmorZeroCount χ a : ℝ)) * f b +
      ∫ u in a..b, ((bmorZeroCount χ u : ℝ) - (bmorZeroCount χ a : ℝ)) * (-f' u) := by
  classical
  let S := (bmorCriticalZerosUpTo χ b).filter (fun ρ => a < |ρ.im|)
  have hneg_cont : ContinuousOn (fun u => -f' u) (Set.Icc a b) := hf'_cont.neg
  -- Pointwise equality on `Icc a b` between the counting-difference integrand and indicator sum
  have hfun_eq : ∀ u ∈ Set.Icc a b,
      ((bmorZeroCount χ u : ℝ) - (bmorZeroCount χ a : ℝ)) * (-f' u) =
      ∑ ρ ∈ S, Set.indicator (Set.Ici |ρ.im|) (fun v => (bmorZeroMult χ ρ : ℝ) * (-f' v)) u := by
    intro u hu
    rw [← bmorZeroCount_Band_eq χ hu.1 hu.2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases hle : |ρ.im| ≤ u
    · have hm : u ∈ Set.Ici |ρ.im| := hle
      rw [Set.indicator_of_mem hm, if_pos hle]
    · have hnm : u ∉ Set.Ici |ρ.im| := hle
      rw [Set.indicator_of_notMem hnm, if_neg hle, zero_mul]
  have hint_sum : IntervalIntegrable
      (∑ ρ ∈ S, fun u => Set.indicator (Set.Ici |ρ.im|) (fun v => (bmorZeroMult χ ρ : ℝ) * (-f' v)) u)
      volume a b :=
    IntervalIntegrable.sum S fun ρ _ =>
      indicator_Ici_intervalIntegrable hab (continuousOn_const.mul hneg_cont)
  have hint : IntervalIntegrable
      (fun u => ((bmorZeroCount χ u : ℝ) - (bmorZeroCount χ a : ℝ)) * (-f' u)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hint_sum ⊢
    refine hint_sum.congr_fun (fun u hu => ?_) measurableSet_Icc
    simp only [Finset.sum_apply]
    exact (hfun_eq u hu).symm
  refine ⟨hint, ?_⟩
  have hint_eq : (∫ u in a..b, ((bmorZeroCount χ u : ℝ) - (bmorZeroCount χ a : ℝ)) * (-f' u)) =
      ∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * ∫ u in |ρ.im|..b, (-f' u) := by
    have hcongr : (∫ u in a..b, ((bmorZeroCount χ u : ℝ) - (bmorZeroCount χ a : ℝ)) * (-f' u)) =
        ∫ u in a..b, ∑ ρ ∈ S, Set.indicator (Set.Ici |ρ.im|)
          (fun v => (bmorZeroMult χ ρ : ℝ) * (-f' v)) u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hab] at hu
      exact hfun_eq u hu
    rw [hcongr, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hmem := Finset.mem_filter.mp hρ
      have hat : a ≤ |ρ.im| := hmem.2.le
      have htb : |ρ.im| ≤ b := (mem_bmorCriticalZerosUpTo χ b ρ |>.mp hmem.1).2
      have hind_mul : (fun u => Set.indicator (Set.Ici |ρ.im|)
          (fun v => (bmorZeroMult χ ρ : ℝ) * (-f' v)) u) =
          fun u => (bmorZeroMult χ ρ : ℝ) * Set.indicator (Set.Ici |ρ.im|) (fun v => -f' v) u := by
        ext u; by_cases h : u ∈ Set.Ici |ρ.im| <;> simp [h]
      rw [hind_mul, intervalIntegral.integral_const_mul,
          integral_indicator_Ici_eq hat htb hneg_cont]
    · intro ρ _
      exact indicator_Ici_intervalIntegrable hab (continuousOn_const.mul hneg_cont)
  rw [hint_eq]
  have hcount_b : (bmorZeroCount χ b : ℝ) - (bmorZeroCount χ a : ℝ) =
      ∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) := by
    have hb := bmorZeroCount_Band_eq χ hab le_rfl
    rw [← hb]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have htb : |ρ.im| ≤ b := (mem_bmorCriticalZerosUpTo χ b ρ |>.mp (Finset.mem_filter.mp hρ).1).2
    simp [htb]
  rw [hcount_b, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hmem := Finset.mem_filter.mp hρ
  have hat : a ≤ |ρ.im| := hmem.2.le
  have htb : |ρ.im| ≤ b := (mem_bmorCriticalZerosUpTo χ b ρ |>.mp hmem.1).2
  have hftc : (∫ u in |ρ.im|..b, (-f' u)) = f |ρ.im| - f b := by
    have hd : ∀ u ∈ Set.uIcc |ρ.im| b, HasDerivAt (fun v => -f v) (-f' u) u := by
      intro u hu
      rw [Set.uIcc_of_le htb] at hu
      exact (hf_deriv u ⟨hat.trans hu.1, hu.2⟩).neg
    have hi : IntervalIntegrable (fun v => -f' v) volume |ρ.im| b :=
      (hneg_cont.mono (Set.Icc_subset_Icc_left hat)).intervalIntegrable_of_Icc htb
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    ring
  rw [hftc]
  ring

/-- Upper majorant `M_Q(u)` on `N(u, χ)` for `d ≤ Q` and `u ≥ 1`. -/
private def bmorZeroUpperMajorant (Q u : ℝ) : ℝ :=
  (u / Real.pi) * (Real.log Q + Real.log u - (Real.log (2 * Real.pi) + 1)) +
    bmorC1 * (Real.log Q + Real.log u) + bmorC2

private theorem bmorZeroCount_le_majorant (h25 : BMORProp2_5)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {Q u : ℝ}
    (hdQ : (χ.conductor : ℝ) ≤ Q) (hu : 1 ≤ u) :
    (bmorZeroCount χ u : ℝ) ≤ bmorZeroUpperMajorant Q u := by
  have hd_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero)
  have hQ_pos : 0 < Q := lt_of_lt_of_le hd_pos hdQ
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have h := (abs_lt.mp (h25 q χ u hu)).2
  have hlog_du : Real.log ((χ.conductor : ℝ) * u) = Real.log (χ.conductor : ℝ) + Real.log u :=
    Real.log_mul hd_pos.ne' hu_pos.ne'
  have hlog_quot : Real.log (((χ.conductor : ℝ) * u) / (2 * Real.pi * Real.exp 1)) =
      Real.log (χ.conductor : ℝ) + Real.log u - (Real.log (2 * Real.pi) + 1) := by
    rw [Real.log_div (mul_pos hd_pos hu_pos).ne' (by positivity), hlog_du,
        Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  have hlog_mono : Real.log (χ.conductor : ℝ) ≤ Real.log Q := Real.log_le_log hd_pos hdQ
  unfold bmorZeroUpperMajorant
  rw [hlog_du, hlog_quot] at h
  have hpi_pos : 0 < u / Real.pi := div_pos hu_pos Real.pi_pos
  have hc1_pos : 0 < bmorC1 := by unfold bmorC1; norm_num
  nlinarith

/-- Derivation of `(LZ1)`–`(LZ3)`: if `χ` satisfies `GRH(H)` with `1 ≤ H` and `d ≤ Q`,
    then `∑_{|γ| ≤ H} m(ρ) / |ρ| ≤ bmorLowZeroCap Q H`. -/
private theorem bmor_low_zero_sum_le_cap (h25 : BMORProp2_5)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {Q H : ℝ}
    (hdQ : (χ.conductor : ℝ) ≤ Q) (hH : 1 ≤ H) (hgrh : bmorSatisfiesGRH χ H) :
    (∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖)) ≤
      bmorLowZeroCap Q H := by
  classical
  have hd_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero)
  have hQ_pos : 0 < Q := lt_of_lt_of_le hd_pos hdQ
  have hH_pos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  -- Split `|γ| ≤ H` into `|γ| ≤ 1` and `1 < |γ| ≤ H`
  let S_le1 := (bmorCriticalZerosUpTo χ H).filter (fun ρ => |ρ.im| ≤ 1)
  let S_gt1 := (bmorCriticalZerosUpTo χ H).filter (fun ρ => 1 < |ρ.im|)
  have hpart : (∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖)) =
      (∑ ρ ∈ S_le1, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖)) +
      (∑ ρ ∈ S_gt1, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖)) := by
    rw [← Finset.sum_union]
    · congr 1; ext ρ; simp only [S_le1, S_gt1, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h; exact (le_or_gt |ρ.im| 1).imp (fun h1 => ⟨h, h1⟩) (fun h2 => ⟨h, h2⟩)
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · rw [Finset.disjoint_left]
      intro ρ h1 h2
      have ha := (Finset.mem_filter.mp h1).2
      have hb := (Finset.mem_filter.mp h2).2
      linarith
  -- On `|γ| ≤ 1`: `S_le1 = bmorCriticalZerosUpTo χ 1` and `1 / ‖ρ‖ ≤ 2` since `Re ρ = 1/2`
  have hS_le1_eq : S_le1 = bmorCriticalZerosUpTo χ 1 := by
    ext ρ; simp only [S_le1, Finset.mem_filter, mem_bmorCriticalZerosUpTo]
    exact ⟨fun ⟨⟨hc, _⟩, h1⟩ => ⟨hc, h1⟩, fun ⟨hc, h1⟩ => ⟨⟨hc, h1.trans hH⟩, h1⟩⟩
  have hlow1 : (∑ ρ ∈ S_le1, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖)) ≤ 2 * (bmorZeroCount χ 1 : ℝ) := by
    rw [hS_le1_eq]
    calc
      (∑ ρ ∈ bmorCriticalZerosUpTo χ 1, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖))
        ≤ ∑ ρ ∈ bmorCriticalZerosUpTo χ 1, (bmorZeroMult χ ρ : ℝ) * 2 := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          have hm := (mem_bmorCriticalZerosUpTo χ 1 ρ).mp hρ
          have hre : ρ.re = 1 / 2 := hgrh ρ hm.1 (hm.2.trans hH)
          have hnorm_ge : (1 / 2 : ℝ) ≤ ‖ρ‖ := by
            have := Complex.abs_re_le_norm ρ
            rw [hre] at this; norm_num at this; exact this
          rw [div_le_iff₀ (by linarith)]
          linarith
      _ = 2 * (bmorZeroCount χ 1 : ℝ) := by
          rw [← Finset.sum_mul, mul_comm]; simp [bmorZeroCount]
  -- On `1 < |γ| ≤ H`: `1 / ‖ρ‖ ≤ 1 / |ρ.im|`
  have hlow2_step : (∑ ρ ∈ S_gt1, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖)) ≤
      ∑ ρ ∈ S_gt1, (bmorZeroMult χ ρ : ℝ) * (|ρ.im|)⁻¹ := by
    refine Finset.sum_le_sum fun ρ hρ => ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have him_gt1 : 1 < |ρ.im| := (Finset.mem_filter.mp hρ).2
    have hnorm_ge : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    rw [one_div]
    exact inv_anti₀ (by linarith) hnorm_ge
  -- Apply exact Stieltjes summation on `(1, H]` with `f u = u⁻¹`, `f' u = -(u ^ 2)⁻¹`
  have hf_deriv : ∀ u ∈ Set.Icc (1 : ℝ) H, HasDerivAt (fun v : ℝ => v⁻¹) (-(u ^ 2)⁻¹) u := by
    intro u hu
    have hu_ne : u ≠ 0 := by linarith [hu.1]
    simpa [neg_div, one_div] using hasDerivAt_inv hu_ne
  have hf'_cont : ContinuousOn (fun u : ℝ => -(u ^ 2)⁻¹) (Set.Icc (1 : ℝ) H) := by
    refine ContinuousOn.neg (ContinuousOn.inv₀ (continuousOn_pow 2) ?_)
    intro u hu; exact pow_ne_zero 2 (by linarith [hu.1])
  obtain ⟨hint_diff, hst⟩ := bmor_stieltjes_band_eq χ hH hf_deriv hf'_cont
  simp only [neg_neg] at hint_diff hst
  -- Separate out the `- N(1)` integral `(∫_1^H N(1) * u⁻²) = N(1) * (1 - H⁻¹)`
  have hint_const : IntervalIntegrable (fun u : ℝ => (bmorZeroCount χ 1 : ℝ) * (u ^ 2)⁻¹) volume 1 H := by
    apply IntervalIntegrable.const_mul
    refine (ContinuousOn.inv₀ (continuousOn_pow 2) ?_).intervalIntegrable_of_Icc hH
    intro u hu; exact pow_ne_zero 2 (by linarith [hu.1])
  have hint_N : IntervalIntegrable (fun u : ℝ => (bmorZeroCount χ u : ℝ) * (u ^ 2)⁻¹) volume 1 H := by
    have hadd := hint_diff.add hint_const
    refine hadd.congr fun u _ => ?_
    ring
  have hint_N1_val : (∫ u in (1 : ℝ)..H, (bmorZeroCount χ 1 : ℝ) * (u ^ 2)⁻¹) =
      (bmorZeroCount χ 1 : ℝ) * (1 - H⁻¹) := by
    rw [intervalIntegral.integral_const_mul]
    have hd : ∀ u ∈ Set.uIcc (1 : ℝ) H, HasDerivAt (fun v : ℝ => -v⁻¹) ((u ^ 2)⁻¹) u := by
      intro u hu
      rw [Set.uIcc_of_le hH] at hu
      have hu_ne : u ≠ 0 := by linarith [hu.1]
      exact (hasDerivAt_inv hu_ne).fun_neg.congr_deriv (neg_neg _)
    have hi : IntervalIntegrable (fun u : ℝ => (u ^ 2)⁻¹) volume 1 H := by
      refine (ContinuousOn.inv₀ (continuousOn_pow 2) ?_).intervalIntegrable_of_Icc hH
      intro u hu; exact pow_ne_zero 2 (by linarith [hu.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    ring
  have hLZ2 : (∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖)) ≤
      (bmorZeroCount χ 1 : ℝ) + (bmorZeroCount χ H : ℝ) * H⁻¹ +
      ∫ u in (1 : ℝ)..H, (bmorZeroCount χ u : ℝ) * (u ^ 2)⁻¹ := by
    have hsplit_int : (∫ u in (1 : ℝ)..H, ((bmorZeroCount χ u : ℝ) - (bmorZeroCount χ 1 : ℝ)) * (u ^ 2)⁻¹) =
        (∫ u in (1 : ℝ)..H, (bmorZeroCount χ u : ℝ) * (u ^ 2)⁻¹) -
        (∫ u in (1 : ℝ)..H, (bmorZeroCount χ 1 : ℝ) * (u ^ 2)⁻¹) := by
      rw [← intervalIntegral.integral_sub hint_N hint_const]
      apply intervalIntegral.integral_congr; intro u _; ring
    rw [hsplit_int, hint_N1_val] at hst
    linarith [hpart, hlow1, hlow2_step, hst]
  -- Bound `N(u)` by `bmorZeroUpperMajorant Q u` and evaluate explicitly via FTC
  let ν := Real.log Q
  let c := Real.log (2 * Real.pi) + 1
  let P : ℝ → ℝ := fun u =>
    ((ν + Real.log u - c) ^ 2) / (2 * Real.pi) - (bmorC1 * (ν + Real.log u + 1) + bmorC2) * u⁻¹
  have hM_cont : ContinuousOn (fun u : ℝ => bmorZeroUpperMajorant Q u * (u ^ 2)⁻¹) (Set.Icc 1 H) := by
    unfold bmorZeroUpperMajorant
    have hlog1 : ContinuousOn Real.log (Set.Icc 1 H) :=
      Real.continuousOn_log.mono fun u hu => ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.add (ContinuousOn.add ?_ ?_) continuousOn_const
      · exact (continuousOn_id.div_const _).mul
          ((continuousOn_const.add hlog1).sub continuousOn_const)
      · exact continuousOn_const.mul (continuousOn_const.add hlog1)
    · refine ContinuousOn.inv₀ (continuousOn_pow 2) fun u hu => pow_ne_zero 2 (by linarith [hu.1])
  have hint_M : IntervalIntegrable (fun u : ℝ => bmorZeroUpperMajorant Q u * (u ^ 2)⁻¹) volume 1 H :=
    hM_cont.intervalIntegrable_of_Icc hH
  have hint_mono : (∫ u in (1 : ℝ)..H, (bmorZeroCount χ u : ℝ) * (u ^ 2)⁻¹) ≤
      ∫ u in (1 : ℝ)..H, bmorZeroUpperMajorant Q u * (u ^ 2)⁻¹ := by
    refine intervalIntegral.integral_mono_on hH hint_N hint_M fun u hu => ?_
    exact mul_le_mul_of_nonneg_right (bmorZeroCount_le_majorant h25 χ hdQ hu.1) (by positivity)
  have hP_deriv : ∀ u ∈ Set.uIcc (1 : ℝ) H,
      HasDerivAt P (bmorZeroUpperMajorant Q u * (u ^ 2)⁻¹) u := by
    intro u hu
    rw [Set.uIcc_of_le hH] at hu
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    have hu_ne : u ≠ 0 := hu_pos.ne'
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hd1 : HasDerivAt (fun v => ν + Real.log v - c) u⁻¹ u :=
      ((Real.hasDerivAt_log hu_ne).const_add ν).sub_const c
    have hd_part1 := (hd1.pow 2).div_const (2 * Real.pi)
    have hd2a : HasDerivAt (fun v => bmorC1 * (ν + Real.log v + 1) + bmorC2) (bmorC1 * u⁻¹) u :=
      ((((Real.hasDerivAt_log hu_ne).const_add ν).add_const 1).const_mul bmorC1).add_const bmorC2
    have hd_part2 := hd2a.mul (hasDerivAt_inv hu_ne)
    have hd := hd_part1.fun_sub hd_part2
    refine hd.congr_deriv ?_
    unfold bmorZeroUpperMajorant
    dsimp [ν, c]
    field_simp [hu_ne, hpi_ne]
    ring
  have hint_P_val : (∫ u in (1 : ℝ)..H, bmorZeroUpperMajorant Q u * (u ^ 2)⁻¹) = P H - P 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hP_deriv hint_M
  have hN1_le : (bmorZeroCount χ 1 : ℝ) ≤ bmorZeroUpperMajorant Q 1 :=
    bmorZeroCount_le_majorant h25 χ hdQ le_rfl
  have hNH_le : (bmorZeroCount χ H : ℝ) * H⁻¹ ≤ bmorZeroUpperMajorant Q H * H⁻¹ :=
    mul_le_mul_of_nonneg_right (bmorZeroCount_le_majorant h25 χ hdQ hH) (inv_nonneg.mpr hH_pos.le)
  have hlog_QH : Real.log (Q * H) = ν + Real.log H := Real.log_mul hQ_pos.ne' hH_pos.ne'
  have halg : bmorZeroUpperMajorant Q 1 + bmorZeroUpperMajorant Q H * H⁻¹ + (P H - P 1) =
      bmorLowZeroCap Q H := by
    unfold bmorZeroUpperMajorant bmorLowZeroCap
    dsimp [P, ν, c]
    rw [hlog_QH, Real.log_one]
    have hH_ne : H ≠ 0 := hH_pos.ne'
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp [hH_ne, hpi_ne]
    ring
  linarith

/-- Unified high-zero power-weighted Stieltjes bound `(SM3)`–`(SM4)`:
    for `1000 ≤ H ≤ T`, `d ≤ Q`, `log(Q * H) ≤ Λ₀`, `0 < Λ₀`, `1 ≤ r`, and `0 < a`,
    `∑_{H < |γ| ≤ T} m(ρ) * H^{-r-1} * (|γ|/H)^{-a-1}` is bounded by
    `H^{-r} * (((Λ₀ / a + 1 / a^2) / π) + 2 * (bmorC1 * Λ₀ + bmorC2) / H)`. -/
private theorem bmor_high_zero_power_sum_le (h25 : BMORProp2_5)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Q H T Λ₀ a : ℝ} {r : ℕ}
    (hdQ : (χ.conductor : ℝ) ≤ Q)
    (hH1000 : 1000 ≤ H) (hHT : H ≤ T)
    (hΛ : Real.log (Q * H) ≤ Λ₀)
    (ha : 0 < a) :
    (∑ ρ ∈ (bmorCriticalZerosUpTo χ T).filter (fun ρ => H < |ρ.im|),
        (bmorZeroMult χ ρ : ℝ) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-a - 1))) ≤
      (H ^ r)⁻¹ * (((Λ₀ / a + 1 / a ^ 2) / Real.pi) + 2 * (bmorC1 * Λ₀ + bmorC2) / H) := by
  classical
  have hd_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero)
  have hQ_pos : 0 < Q := lt_of_lt_of_le hd_pos hdQ
  have hH_pos : 0 < H := by linarith
  have hΛ_pos : 0 < Λ₀ := by
    have hQH_gt1 : 1 < Q * H := by
      have hd1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
      nlinarith
    exact lt_of_lt_of_le (Real.log_pos hQH_gt1) hΛ
  -- Define `f u = (H ^ (r + 1))⁻¹ * (u / H) ^ (-a - 1)` on `[H, T]`
  let K : ℝ := (H ^ (r + 1))⁻¹
  have hK_nonneg : 0 ≤ K := by dsimp [K]; positivity
  let f : ℝ → ℝ := fun u => K * (u / H) ^ (-a - 1)
  let f' : ℝ → ℝ := fun u => K * ((-a - 1) / H * (u / H) ^ (-a - 2))
  have hf_deriv : ∀ u ∈ Set.Icc H T, HasDerivAt f (f' u) u := by
    intro u hu
    have huH_pos : 0 < u / H := div_pos (by linarith [hu.1]) hH_pos
    have hd_div : HasDerivAt (fun v => v / H) (1 / H) u :=
      (hasDerivAt_id u).div_const H
    have hd := (hd_div.rpow_const (p := -a - 1) (.inl huH_pos.ne')).const_mul K
    refine hd.congr_deriv ?_
    dsimp [f']
    have hexp : -a - 1 - 1 = -a - 2 := by ring
    rw [hexp]
    ring
  have hf'_cont : ContinuousOn f' (Set.Icc H T) := by
    dsimp [f']
    refine continuousOn_const.mul (continuousOn_const.mul ?_)
    refine ContinuousOn.rpow_const (continuousOn_id.div_const H) fun u hu => .inl ?_
    exact (div_pos (by linarith [hu.1]) hH_pos).ne'
  obtain ⟨hint_diff, hst⟩ := bmor_stieltjes_band_eq χ hHT hf_deriv hf'_cont
  -- Retain actual primitive conductor `d` in `F_d(u)` and `E_Q(u)` (`(SM3)`)
  let d : ℝ := (χ.conductor : ℝ)
  let F_d : ℝ → ℝ := fun u => (u / Real.pi) * (Real.log d + Real.log u - (Real.log (2 * Real.pi) + 1))
  let F_d' : ℝ → ℝ := fun u => (Real.log d + Real.log u - Real.log (2 * Real.pi)) / Real.pi
  let E_Q : ℝ → ℝ := fun u => bmorC1 * (Real.log Q + Real.log u) + bmorC2
  -- Two-sided bound `N(u) - N(H) ≤ (F_d(u) - F_d(H)) + (E_Q(u) + E_Q(H))` for `u ≥ H`
  have hNR_bound : ∀ u : ℝ, H ≤ u →
      (bmorZeroCount χ u : ℝ) - (bmorZeroCount χ H : ℝ) ≤
        (F_d u - F_d H) + (E_Q u + E_Q H) := by
    intro u huH
    have hu1 : 1 ≤ u := by linarith
    have hH1 : 1 ≤ H := by linarith
    have hu_pos : 0 < u := by linarith
    have h1 := (abs_lt.mp (h25 q χ u hu1)).2
    have h2 := (abs_lt.mp (h25 q χ H hH1)).1
    have hlog_du : Real.log (d * u) = Real.log d + Real.log u :=
      Real.log_mul hd_pos.ne' hu_pos.ne'
    have hlog_dH : Real.log (d * H) = Real.log d + Real.log H :=
      Real.log_mul hd_pos.ne' hH_pos.ne'
    have hq_u : Real.log ((d * u) / (2 * Real.pi * Real.exp 1)) =
        Real.log d + Real.log u - (Real.log (2 * Real.pi) + 1) := by
      rw [Real.log_div (mul_pos hd_pos hu_pos).ne' (by positivity), hlog_du,
          Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    have hq_H : Real.log ((d * H) / (2 * Real.pi * Real.exp 1)) =
        Real.log d + Real.log H - (Real.log (2 * Real.pi) + 1) := by
      rw [Real.log_div (mul_pos hd_pos hH_pos).ne' (by positivity), hlog_dH,
          Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    rw [hlog_du, hq_u] at h1
    rw [hlog_dH, hq_H] at h2
    have hlog_dQ : Real.log d ≤ Real.log Q := Real.log_le_log hd_pos hdQ
    have hc1_pos : 0 < bmorC1 := by unfold bmorC1; norm_num
    dsimp [F_d, E_Q]
    nlinarith
  have hneg_f'_nonneg : ∀ u ∈ Set.Icc H T, 0 ≤ -f' u := by
    intro u hu
    dsimp [f']
    have huH_pos : 0 < u / H := div_pos (by linarith [hu.1]) hH_pos
    have h1 : - (K * ((-a - 1) / H * (u / H) ^ (-a - 2))) =
        K * ((a + 1) / H * (u / H) ^ (-a - 2)) := by ring
    rw [h1]
    positivity
  have hfT_nonneg : 0 ≤ f T := by
    dsimp [f]
    have hTH_pos : 0 < T / H := div_pos (by linarith) hH_pos
    positivity
  let M_diff : ℝ → ℝ := fun u => (F_d u - F_d H) + (E_Q u + E_Q H)
  have hM_diff_cont : ContinuousOn M_diff (Set.Icc H T) := by
    dsimp [M_diff, F_d, E_Q]
    have hlog_cont : ContinuousOn Real.log (Set.Icc H T) :=
      Real.continuousOn_log.mono fun u hu => ne_of_gt (lt_of_lt_of_le hH_pos hu.1)
    fun_prop
  have hint_M_diff : IntervalIntegrable (fun u => M_diff u * (-f' u)) volume H T :=
    (hM_diff_cont.mul hf'_cont.neg).intervalIntegrable_of_Icc hHT
  have hstep1 : (∑ ρ ∈ (bmorCriticalZerosUpTo χ T).filter (fun ρ => H < |ρ.im|),
      (bmorZeroMult χ ρ : ℝ) * f |ρ.im|) ≤
      M_diff T * f T + ∫ u in H..T, M_diff u * (-f' u) := by
    have hbnd_T : ((bmorZeroCount χ T : ℝ) - (bmorZeroCount χ H : ℝ)) * f T ≤ M_diff T * f T :=
      mul_le_mul_of_nonneg_right (hNR_bound T hHT) hfT_nonneg
    have hbnd_int : (∫ u in H..T, ((bmorZeroCount χ u : ℝ) - (bmorZeroCount χ H : ℝ)) * (-f' u)) ≤
        ∫ u in H..T, M_diff u * (-f' u) := by
      refine intervalIntegral.integral_mono_on hHT hint_diff hint_M_diff fun u hu => ?_
      exact mul_le_mul_of_nonneg_right (hNR_bound u hu.1) (hneg_f'_nonneg u hu)
    linarith [hst]
  -- Integration by parts on `M_diff * f`:
  -- `d/du (M_diff u * f u) = (F_d' u + bmorC1 / u) * f u + M_diff u * f' u`
  have hM_ibp_deriv : ∀ u ∈ Set.uIcc H T,
      HasDerivAt (fun v => M_diff v * f v) ((F_d' u + bmorC1 * u⁻¹) * f u + M_diff u * f' u) u := by
    intro u hu
    rw [Set.uIcc_of_le hHT] at hu
    have hu_pos : 0 < u := by linarith [hu.1]
    have hu_ne : u ≠ 0 := hu_pos.ne'
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hd_Fd : HasDerivAt F_d (F_d' u) u := by
      dsimp [F_d, F_d']
      have h1 : HasDerivAt (fun v => v / Real.pi) (1 / Real.pi) u :=
        (hasDerivAt_id u).div_const Real.pi
      have h2 : HasDerivAt (fun v => Real.log d + Real.log v - (Real.log (2 * Real.pi) + 1)) u⁻¹ u :=
        ((Real.hasDerivAt_log hu_ne).const_add (Real.log d)).sub_const _
      refine (h1.mul h2).congr_deriv ?_
      field_simp [hu_ne, hpi_ne]
      ring
    have hd_EQ : HasDerivAt E_Q (bmorC1 * u⁻¹) u := by
      dsimp [E_Q]
      exact (((Real.hasDerivAt_log hu_ne).const_add (Real.log Q)).const_mul bmorC1).add_const bmorC2
    have hd_M : HasDerivAt M_diff (F_d' u + bmorC1 * u⁻¹) u := by
      dsimp [M_diff]
      exact (hd_Fd.sub_const (F_d H)).fun_add (hd_EQ.add_const (E_Q H))
    exact hd_M.mul (hf_deriv u hu)
  have hf_cont : ContinuousOn f (Set.Icc H T) := by
    dsimp [f]
    refine continuousOn_const.mul ?_
    refine ContinuousOn.rpow_const (continuousOn_id.div_const H) fun u hu => .inl ?_
    exact (div_pos (by linarith [hu.1]) hH_pos).ne'
  have hint_main : IntervalIntegrable (fun u => (F_d' u + bmorC1 * u⁻¹) * f u) volume H T := by
    refine (ContinuousOn.mul ?_ hf_cont).intervalIntegrable_of_Icc hHT
    dsimp [F_d']
    have hlog_cont : ContinuousOn Real.log (Set.Icc H T) :=
      Real.continuousOn_log.mono fun u hu => ne_of_gt (lt_of_lt_of_le hH_pos hu.1)
    have hinv_cont : ContinuousOn (fun u : ℝ => u⁻¹) (Set.Icc H T) :=
      ContinuousOn.inv₀ continuousOn_id fun u hu => ne_of_gt (lt_of_lt_of_le hH_pos hu.1)
    fun_prop
  have hint_Mf' : IntervalIntegrable (fun u => M_diff u * f' u) volume H T :=
    (hM_diff_cont.mul hf'_cont).intervalIntegrable_of_Icc hHT
  have hibp : (∫ u in H..T, ((F_d' u + bmorC1 * u⁻¹) * f u + M_diff u * f' u)) =
      M_diff T * f T - M_diff H * f H :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hM_ibp_deriv (hint_main.add hint_Mf')
  have hsplit_ibp : (∫ u in H..T, ((F_d' u + bmorC1 * u⁻¹) * f u + M_diff u * f' u)) =
      (∫ u in H..T, (F_d' u + bmorC1 * u⁻¹) * f u) - (∫ u in H..T, M_diff u * (-f' u)) := by
    rw [intervalIntegral.integral_add hint_main hint_Mf']
    congr 1
    have hneg_eq : (fun u => M_diff u * f' u) = fun u => -(M_diff u * (-f' u)) := by
      ext u; ring
    rw [hneg_eq, intervalIntegral.integral_neg]
  have hMH_fH : M_diff H * f H = 2 * E_Q H * K := by
    dsimp [M_diff, f]
    rw [div_self hH_pos.ne', Real.one_rpow]
    ring
  have hstep2 : M_diff T * f T + (∫ u in H..T, M_diff u * (-f' u)) =
      2 * E_Q H * K + ∫ u in H..T, (F_d' u + bmorC1 * u⁻¹) * f u := by
    linarith [hibp, hsplit_ibp, hMH_fH]
  -- Pointwise absorb `bmorC1 / u - log(2*pi) / pi < 0` on `u ≥ H ≥ 1000`
  have h2pi_gt_e : Real.exp 1 ≤ 2 * Real.pi := by
    have hpi3 : (3 : ℝ) < Real.pi := by
      have h := Real.pi_gt_d2; norm_num at h; linarith
    have he3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  have hlog2pi_ge1 : 1 ≤ Real.log (2 * Real.pi) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) h2pi_gt_e
  have hpi_lt4 : Real.pi < 4 := by
    have h := Real.pi_lt_d2; norm_num at h; linarith
  let g_dom : ℝ → ℝ := fun u => ((Λ₀ + Real.log (u / H)) / Real.pi) * f u
  have hg_dom_cont : ContinuousOn g_dom (Set.Icc H T) := by
    dsimp [g_dom]
    refine ContinuousOn.mul ?_ hf_cont
    refine (continuousOn_const.add ?_).div_const Real.pi
    exact Real.continuousOn_log.comp (continuousOn_id.div_const H) fun u hu =>
      (div_pos (by linarith [hu.1]) hH_pos).ne'
  have hint_g_dom : IntervalIntegrable g_dom volume H T :=
    hg_dom_cont.intervalIntegrable_of_Icc hHT
  have hint_dom_le : (∫ u in H..T, (F_d' u + bmorC1 * u⁻¹) * f u) ≤ ∫ u in H..T, g_dom u := by
    refine intervalIntegral.integral_mono_on hHT hint_main hint_g_dom fun u hu => ?_
    have hu_pos : 0 < u := by linarith [hu.1]
    have hfu_nonneg : 0 ≤ f u := by
      dsimp [f]; have : 0 < u / H := div_pos hu_pos hH_pos; positivity
    apply mul_le_mul_of_nonneg_right _ hfu_nonneg
    dsimp [F_d']
    have hlog_u : Real.log u = Real.log H + Real.log (u / H) := by
      rw [Real.log_div hu_pos.ne' hH_pos.ne']; ring
    have hlog_dH : Real.log d + Real.log H ≤ Λ₀ := by
      have hdQ_log : Real.log d ≤ Real.log Q := Real.log_le_log hd_pos hdQ
      have hQH : Real.log (Q * H) = Real.log Q + Real.log H := Real.log_mul hQ_pos.ne' hH_pos.ne'
      linarith
    have hinv_u : u⁻¹ ≤ (1000 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (hH1000.trans hu.1)
    have hc1_term : bmorC1 * u⁻¹ ≤ 1 / 4 := by
      unfold bmorC1; linarith
    have h2pi_term : 1 / 4 ≤ Real.log (2 * Real.pi) / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      linarith
    have h1 : (Real.log d + Real.log u - Real.log (2 * Real.pi)) / Real.pi + bmorC1 * u⁻¹ =
        (Real.log d + Real.log H + Real.log (u / H)) / Real.pi +
        (bmorC1 * u⁻¹ - Real.log (2 * Real.pi) / Real.pi) := by
      rw [hlog_u]; ring
    rw [h1]
    have h2 : (Real.log d + Real.log H + Real.log (u / H)) / Real.pi ≤
        (Λ₀ + Real.log (u / H)) / Real.pi :=
      div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    linarith
  -- Explicit antiderivative `G_a(u) = -(H ^ (-r)) / pi * ((Λ₀ + log(u/H))/a + 1/a^2) * (u/H)^(-a)`
  let G_a : ℝ → ℝ := fun u =>
    -((H ^ r)⁻¹ / Real.pi) * (((Λ₀ + Real.log (u / H)) / a + 1 / a ^ 2) * (u / H) ^ (-a))
  have hGa_deriv : ∀ u ∈ Set.uIcc H T, HasDerivAt G_a (g_dom u) u := by
    intro u hu
    rw [Set.uIcc_of_le hHT] at hu
    have hu_pos : 0 < u := by linarith [hu.1]
    have hu_ne : u ≠ 0 := hu_pos.ne'
    have hH_ne : H ≠ 0 := hH_pos.ne'
    have ha_ne : a ≠ 0 := ha.ne'
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    have huH_pos : 0 < u / H := div_pos hu_pos hH_pos
    have hd_div : HasDerivAt (fun v => v / H) (1 / H) u :=
      (hasDerivAt_id u).div_const H
    have hd_log := hd_div.log huH_pos.ne'
    have hd_lin := ((hd_log.const_add Λ₀).div_const a).add_const (1 / a ^ 2)
    have hd_pow := hd_div.rpow_const (p := -a) (.inl huH_pos.ne')
    have hd := (hd_lin.mul hd_pow).const_mul (-((H ^ r)⁻¹ / Real.pi))
    refine hd.congr_deriv ?_
    dsimp [g_dom, f, K]
    have hrpow_step : (u / H) ^ (-a) = (u / H) ^ (-a - 1) * (u / H) := by
      have hexp : -a = (-a - 1) + 1 := by ring
      conv_lhs => rw [hexp]
      rw [Real.rpow_add huH_pos, Real.rpow_one]
    rw [hrpow_step, pow_succ]
    field_simp [hu_ne, hH_ne, ha_ne, hpi_ne]
    ring
  have hint_Ga_val : (∫ u in H..T, g_dom u) = G_a T - G_a H :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hGa_deriv hint_g_dom
  have hGa_T_nonpos : G_a T ≤ 0 := by
    dsimp [G_a]
    have hTH_ge1 : 1 ≤ T / H := (one_le_div hH_pos).mpr hHT
    have hlog_nonneg : 0 ≤ Real.log (T / H) := Real.log_nonneg hTH_ge1
    have hTH_pos : 0 < T / H := lt_of_lt_of_le zero_lt_one hTH_ge1
    have hpos : 0 ≤ ((H ^ r)⁻¹ / Real.pi) *
        (((Λ₀ + Real.log (T / H)) / a + 1 / a ^ 2) * (T / H) ^ (-a)) := by positivity
    linarith
  have hGa_H_val : -G_a H = (H ^ r)⁻¹ * ((Λ₀ / a + 1 / a ^ 2) / Real.pi) := by
    dsimp [G_a]
    rw [div_self hH_pos.ne', Real.log_one, add_zero, Real.one_rpow, mul_one]
    ring
  have hEQ_H_le : 2 * E_Q H * K ≤ (H ^ r)⁻¹ * (2 * (bmorC1 * Λ₀ + bmorC2) / H) := by
    dsimp [E_Q, K]
    have hQH : Real.log Q + Real.log H = Real.log (Q * H) :=
      (Real.log_mul hQ_pos.ne' hH_pos.ne').symm
    rw [hQH, pow_succ, mul_inv]
    have hc1_pos : 0 < bmorC1 := by unfold bmorC1; norm_num
    have h1 : 2 * (bmorC1 * Real.log (Q * H) + bmorC2) ≤ 2 * (bmorC1 * Λ₀ + bmorC2) := by nlinarith
    calc
      2 * (bmorC1 * Real.log (Q * H) + bmorC2) * ((H ^ r)⁻¹ * H⁻¹)
        ≤ 2 * (bmorC1 * Λ₀ + bmorC2) * ((H ^ r)⁻¹ * H⁻¹) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (H ^ r)⁻¹ * (2 * (bmorC1 * Λ₀ + bmorC2) / H) := by ring
  linarith [hstep1, hstep2, hint_dom_le, hint_Ga_val, hGa_T_nonpos, hGa_H_val, hEQ_H_le]

/-! ## 5. Summability of `bmorUTerm` and Bounds on `bmorU`, `bmorV`, and `bmorW` -/

/-- Product denominator bound `∏_{j=0}^m ‖ρ + j‖ ≥ |Im ρ| ^ (m + 1)`. -/
private theorem prod_norm_add_ge_abs_im_pow (ρ : ℂ) (m : ℕ) :
    |ρ.im| ^ (m + 1) ≤ ∏ j ∈ Finset.range (m + 1), ‖ρ + (j : ℂ)‖ := by
  have h1 : |ρ.im| ^ (m + 1) = ∏ _j ∈ Finset.range (m + 1), |ρ.im| := by simp
  rw [h1]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => ?_
  have him : (ρ + (j : ℂ)).im = ρ.im := by simp
  simpa [him] using Complex.abs_im_le_norm (ρ + (j : ℂ))

theorem bmorUTerm_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (m : ℕ) {x : ℝ} (hx : 0 < x) (H : ℝ) (ρ : ℂ) :
    0 ≤ bmorUTerm χ m x H ρ := by
  unfold bmorUTerm
  split_ifs
  · apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg (Real.rpow_pos_of_pos hx _).le
    exact Finset.prod_nonneg fun _ _ => norm_nonneg _
  · rfl

/-- General passage from a uniform finite-height bound on `(H, T]` to `Summable` and `tsum ≤ C`. -/
private theorem bmorUTerm_summable_and_tsum_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (m : ℕ) {x H C : ℝ} (hx : 0 < x)
    (hfin : ∀ T : ℝ, H ≤ T →
      (∑ ρ ∈ (bmorCriticalZerosUpTo χ T).filter (fun ρ => H < |ρ.im|),
        bmorUTerm χ m x H ρ) ≤ C) :
    Summable (bmorUTerm χ m x H) ∧ (∑' ρ : ℂ, bmorUTerm χ m x H ρ) ≤ C := by
  classical
  have hnn : ∀ ρ : ℂ, 0 ≤ bmorUTerm χ m x H ρ := fun ρ => bmorUTerm_nonneg χ m hx H ρ
  have hsum_le : ∀ F : Finset ℂ, (∑ ρ ∈ F, bmorUTerm χ m x H ρ) ≤ C := by
    intro F
    let F' := F.filter (fun ρ => 0 < bmorZeroMult χ ρ ∧ H < |ρ.im|)
    have heq : (∑ ρ ∈ F, bmorUTerm χ m x H ρ) = ∑ ρ ∈ F', bmorUTerm χ m x H ρ := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ F) fun ρ _ hnot => ?_
      simp only [F', Finset.mem_filter, not_and_or] at hnot
      rcases hnot with hf | hnot_pos | hnot_H
      · exact False.elim (hf ‹ρ ∈ F›)
      · have hm0 : bmorZeroMult χ ρ = 0 := by omega
        simp [bmorUTerm, hm0]
      · simp [bmorUTerm, hnot_H]
    let T : ℝ := max H 0 + 1 + ∑ ρ ∈ F, |ρ.im|
    have hHT : H ≤ T := by
      have : 0 ≤ ∑ ρ ∈ F, |ρ.im| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have : H ≤ max H 0 := le_max_left H 0
      dsimp [T]; linarith
    have hsub : F' ⊆ (bmorCriticalZerosUpTo χ T).filter (fun ρ => H < |ρ.im|) := by
      intro ρ hρ
      have hm := Finset.mem_filter.mp hρ
      rw [Finset.mem_filter, mem_bmorCriticalZerosUpTo]
      refine ⟨⟨(bmorZeroMult_pos_iff χ ρ).mp hm.2.1, ?_⟩, hm.2.2⟩
      have hle_sum : |ρ.im| ≤ ∑ σ ∈ F, |σ.im| :=
        Finset.single_le_sum (f := fun σ : ℂ => |σ.im|) (fun _ _ => abs_nonneg _) hm.1
      have : 0 ≤ max H 0 := le_max_right H 0
      dsimp [T]; linarith
    rw [heq]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => hnn ρ)).trans (hfin T hHT)
  exact ⟨summable_of_sum_le hnn hsum_le, Real.tsum_le_of_sum_le hnn hsum_le⟩

/-- Every series in `bmorU` is genuinely `Summable` for `m ≥ 1` and `x ≥ 1` (never hitting
    Lean's `tsum = 0` junk value). -/
theorem bmorUTerm_summable (h25 : BMORProp2_5)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {m : ℕ} (hm : 1 ≤ m) {x H : ℝ} (hx : 1 ≤ x) :
    Summable (bmorUTerm χ m x H) := by
  classical
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let H' : ℝ := max H 1000
  have hH'1000 : 1000 ≤ H' := le_max_right H 1000
  have hHH' : H ≤ H' := le_max_left H 1000
  let Q : ℝ := (χ.conductor : ℝ)
  let Λ₀ : ℝ := max (Real.log (Q * H')) 1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  let C_tail : ℝ := (H' ^ m)⁻¹ *
    (((Λ₀ / (m : ℝ) + 1 / (m : ℝ) ^ 2) / Real.pi) + 2 * (bmorC1 * Λ₀ + bmorC2) / H')
  let C_low : ℝ := ∑ ρ ∈ bmorCriticalZerosUpTo χ H', bmorUTerm χ m x H ρ
  refine (bmorUTerm_summable_and_tsum_le χ m hx_pos (C := C_low + C_tail) fun T hHT => ?_).1
  let T' : ℝ := max T H'
  have hH'T' : H' ≤ T' := le_max_right T H'
  have hTT' : T ≤ T' := le_max_left T H'
  let S := (bmorCriticalZerosUpTo χ T).filter (fun ρ => H < |ρ.im|)
  have hpart : (∑ ρ ∈ S, bmorUTerm χ m x H ρ) =
      (∑ ρ ∈ S.filter (fun ρ => |ρ.im| ≤ H'), bmorUTerm χ m x H ρ) +
      (∑ ρ ∈ S.filter (fun ρ => H' < |ρ.im|), bmorUTerm χ m x H ρ) := by
    rw [← Finset.sum_union]
    · congr 1; ext ρ; simp only [Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => (le_or_gt |ρ.im| H').imp (fun h1 => ⟨h, h1⟩) (fun h2 => ⟨h, h2⟩),
             fun h => h.elim And.left And.left⟩
    · rw [Finset.disjoint_left]
      intro ρ h1 h2; linarith [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2]
  have h1 : (∑ ρ ∈ S.filter (fun ρ => |ρ.im| ≤ H'), bmorUTerm χ m x H ρ) ≤ C_low := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ρ _ _ => bmorUTerm_nonneg χ m hx_pos H ρ)
    intro ρ hρ
    have hm1 := Finset.mem_filter.mp hρ
    have hm2 := (mem_bmorCriticalZerosUpTo χ T ρ).mp (Finset.mem_filter.mp hm1.1).1
    exact (mem_bmorCriticalZerosUpTo χ H' ρ).mpr ⟨hm2.1, hm1.2⟩
  have h2 : (∑ ρ ∈ S.filter (fun ρ => H' < |ρ.im|), bmorUTerm χ m x H ρ) ≤ C_tail := by
    have hsub : S.filter (fun ρ => H' < |ρ.im|) ⊆
        (bmorCriticalZerosUpTo χ T').filter (fun ρ => H' < |ρ.im|) := by
      intro ρ hρ
      have hm1 := Finset.mem_filter.mp hρ
      have hm2 := (mem_bmorCriticalZerosUpTo χ T ρ).mp (Finset.mem_filter.mp hm1.1).1
      rw [Finset.mem_filter, mem_bmorCriticalZerosUpTo]
      exact ⟨⟨hm2.1, hm2.2.trans hTT'⟩, hm1.2⟩
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun ρ _ _ => bmorUTerm_nonneg χ m hx_pos H ρ)).trans ?_
    refine (Finset.sum_le_sum fun ρ hρ => ?_).trans
      (bmor_high_zero_power_sum_le h25 χ le_rfl hH'1000 hH'T' (le_max_left _ _) hm_pos)
    have hm1 := Finset.mem_filter.mp hρ
    have hcrit := ((mem_bmorCriticalZerosUpTo χ T' ρ).mp hm1.1).1
    have him_gt_H : H < |ρ.im| := lt_of_le_of_lt hHH' hm1.2
    have him_pos : 0 < |ρ.im| := lt_of_lt_of_le (by linarith) hm1.2.le
    have hH'_pos : 0 < H' := by linarith
    rw [bmorUTerm, if_pos him_gt_H]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hx_le1 : x ^ (ρ.re - 1) ≤ 1 := by
      calc
        x ^ (ρ.re - 1) ≤ x ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith [hcrit.2.1])
        _ = 1 := Real.rpow_zero x
    have hden : |ρ.im| ^ (m + 1) ≤ ∏ j ∈ Finset.range (m + 1), ‖ρ + (j : ℂ)‖ :=
      prod_norm_add_ge_abs_im_pow ρ m
    have hquot : x ^ (ρ.re - 1) / (∏ j ∈ Finset.range (m + 1), ‖ρ + (j : ℂ)‖) ≤
        (|ρ.im| ^ (m + 1))⁻¹ := by
      calc
        x ^ (ρ.re - 1) / (∏ j ∈ Finset.range (m + 1), ‖ρ + (j : ℂ)‖)
          ≤ 1 / (∏ j ∈ Finset.range (m + 1), ‖ρ + (j : ℂ)‖) :=
            div_le_div_of_nonneg_right hx_le1 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        _ ≤ 1 / |ρ.im| ^ (m + 1) :=
            one_div_le_one_div_of_le (pow_pos him_pos _) hden
        _ = (|ρ.im| ^ (m + 1))⁻¹ := one_div _
    have hpow_eq : (|ρ.im| ^ (m + 1))⁻¹ = (H' ^ (m + 1))⁻¹ * (|ρ.im| / H') ^ (-(m : ℝ) - 1) := by
      have hexp : -(m : ℝ) - 1 = -(((m + 1 : ℕ) : ℝ)) := by push_cast; ring
      rw [hexp, Real.rpow_neg (div_pos him_pos hH'_pos).le, Real.rpow_natCast, div_pow, inv_div]
      field_simp [hH'_pos.ne', him_pos.ne']
    exact hquot.trans_eq hpow_eq
  linarith [hpart, h1, h2]

/-- Cardinality of `DirichletCharacter ℂ q` equals `Nat.totient q` for `q ≥ 1`. -/
private theorem card_dirichletCharacter_eq_totient (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- Non-spectral error bound `x * bmorW q x ≤ φ(q) * (25 * log x + 62)` for `1 ≤ q ≤ 100000`
    and `x ≥ 1`. -/
private theorem mul_bmorW_le {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ 100000) {x : ℝ} (hx : 1 ≤ x) :
    x * bmorW q x ≤ (Nat.totient q : ℝ) * (25 * Real.log x + 62) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  unfold bmorW
  have hcancel : x * (((Nat.totient q : ℝ) / x) *
      ((1 / 2 + ∑ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1)) * Real.log x +
        4 * Real.log (q : ℝ) + 67 / 5)) =
      (Nat.totient q : ℝ) *
        ((1 / 2 + ∑ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1)) * Real.log x +
          4 * Real.log (q : ℝ) + 67 / 5) := by
    field_simp [hx_pos.ne']
  rw [hcancel]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  -- Bound `q.primeFactors.card ≤ 16` via `2 ^ card ≤ ∏ p ∈ primeFactors, p ≤ q ≤ 100000 < 2^17`
  have hcard16 : q.primeFactors.card ≤ 16 := by
    have hprod_le : (∏ p ∈ q.primeFactors, p) ≤ q :=
      Nat.le_of_dvd hq1 (Nat.prod_primeFactors_dvd q)
    have hpow_le : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
      have h2 : 2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, 2 := by simp
      rw [h2]
      exact Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    have hlt : 2 ^ q.primeFactors.card < 2 ^ 17 := by omega
    have hlt_exp : q.primeFactors.card < 17 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  have hsum_pf : (∑ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1)) ≤ 16 := by
    calc
      (∑ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1))
        ≤ ∑ _p ∈ q.primeFactors, (1 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          rw [div_le_one (by linarith)]
          linarith
      _ = (q.primeFactors.card : ℝ) := by simp
      _ ≤ 16 := by exact_mod_cast hcard16
  -- Bound `Real.log q ≤ 12` via `19 < exp 3 ⇒ 100000 < 19^4 < exp 12`
  have hlogq_le12 : Real.log (q : ℝ) ≤ 12 := by
    have hexp3 : (19 : ℝ) < Real.exp 3 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 7
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
      norm_num at h
      linarith
    have hexp12 : (q : ℝ) ≤ Real.exp 12 := by
      have hq_real : (q : ℝ) ≤ 100000 := by exact_mod_cast hq
      have hpow : (19 : ℝ) ^ 4 ≤ (Real.exp 3) ^ 4 :=
        pow_le_pow_left₀ (by norm_num) hexp3.le 4
      have hexp_mul : (Real.exp 3) ^ 4 = Real.exp 12 := by
        rw [← Real.exp_nat_mul]; norm_num
      linarith [show (100000 : ℝ) ≤ (19 : ℝ) ^ 4 by norm_num]
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    calc
      Real.log (q : ℝ) ≤ Real.log (Real.exp 12) := Real.log_le_log hq_pos hexp12
      _ = 12 := Real.log_exp 12
  have hpf_logx : (1 / 2 + ∑ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1)) * Real.log x ≤
      25 * Real.log x :=
    mul_le_mul_of_nonneg_right (by linarith) hlogx_nonneg
  linarith

/-! ## 6. Derivation of `BMORExplicitFormulaImports` from `BMORPublishedExplicitFormula` -/

/-- Helper: `exp 14 > 1000`, giving `x > 2` and `δ < (x - 2) / (m * x)` from `14 ≤ log x`
    and `m * δ < 1 / 100`. -/
private theorem smoothing_domain_of_log_ge_14 {x τ : ℝ} {r : ℕ}
    (hx1 : 1 ≤ x) (hlog : 14 ≤ Real.log x) (hr : 1 ≤ r) (_hτ : 0 < τ)
    (hrτ : (r : ℝ) * τ < 1 / 100) :
    2 < x ∧ τ < (x - 2) / ((r : ℝ) * x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hx_gt1000 : 1000 < x := by
    have hexp14 : (1000 : ℝ) < Real.exp 14 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 14) 6
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
      norm_num at h
      linarith
    have hle : Real.exp 14 ≤ x := by
      rw [← Real.exp_log hx_pos]
      exact Real.exp_le_exp.mpr hlog
    linarith
  refine ⟨by linarith, ?_⟩
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  rw [lt_div_iff₀ (mul_pos hr_pos hx_pos)]
  nlinarith

/-- Proof of `BMORSmoothedPsiSmallModuli` from verbatim `BMORPublishedExplicitFormula`. -/
theorem bmorSmoothedPsiSmallModuli_of_published (pub : BMORPublishedExplicitFormula) :
    BMORSmoothedPsiSmallModuli := by
  intro q Q a r τ z x hq3 hqQ hQ hcop hr hτ hrτ hz har hx1 hlog
  have : NeZero q := ⟨by omega⟩
  obtain ⟨hx2, hτ_dom⟩ := smoothing_domain_of_log_ge_14 hx1 (hz.trans hlog) hr hτ hrτ
  have hx_pos : 0 < x := by linarith
  let H : ℝ := (10 ^ 8 : ℝ) / (Q : ℝ)
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hH1000 : 1000 ≤ H := by
    dsimp [H]
    rw [le_div_iff₀ hQ_pos]
    have : (Q : ℝ) ≤ 100000 := by exact_mod_cast hQ
    linarith
  have hH1 : 1 ≤ H := by linarith
  -- Every `χ mod q` satisfies `GRH(H)` (and hence `GRH(1)`) via `BMORProp2_7`
  have hgrh_H : ∀ χ : DirichletCharacter ℂ q, bmorSatisfiesGRH χ H := by
    intro χ
    let d := χ.conductor
    have : NeZero d := ⟨χ.conductor_ne_zero⟩
    have hd_le_q : d ≤ q := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
    have hd_le_Q : d ≤ Q := hd_le_q.trans hqQ
    have hd_100k : d ≤ 100000 := hd_le_Q.trans hQ
    have hprim := pub.prop2_7 d χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hd_100k
    have hH_le_ver : H ≤ bmorVerifiedHeight d := by
      unfold bmorVerifiedHeight
      by_cases hd1 : d = 1
      · rw [if_pos hd1]
        dsimp [H]
        have hQ3 : (3 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (hq3.trans hqQ)
        rw [div_le_iff₀ hQ_pos]
        linarith
      · rw [if_neg hd1, if_pos hd_100k]
        dsimp [H]
        have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero χ.conductor_ne_zero)
        exact div_le_div_of_nonneg_left (by norm_num) hd_pos (by exact_mod_cast hd_le_Q)
    exact bmorSatisfiesGRH_of_primitive χ fun ρ hρ him => hprim ρ hρ (him.trans hH_le_ver)
  have hgrh_1 : ∀ χ : DirichletCharacter ℂ q, bmorSatisfiesGRH χ 1 :=
    fun χ ρ hρ him => hgrh_H χ ρ hρ (him.trans hH1)
  -- Apply `BMORProp2_1` and rewrite `chebyshevPsiAP = psiAP`
  have hexp_formula := (pub.prop2_1 q a r x τ H hcop hx2 hH1 hr hτ hτ_dom hgrh_1).le
  rw [chebyshevPsiAP_eq_psiAP hx2.le q a] at hexp_formula
  -- Multiply both sides by `x > 0`
  have hexp_mul : (Nat.totient q : ℝ) * |psiAP x q a - x / (Nat.totient q : ℝ)| ≤
      (bmorU q r x τ H + (r : ℝ) * τ / 2) * x + x * bmorV q r x τ H + x * bmorW q x := by
    have h := mul_le_mul_of_nonneg_left hexp_formula hx_pos.le
    have hlhs : x * (((Nat.totient q : ℝ) / x) * |psiAP x q a - x / (Nat.totient q : ℝ)|) =
        (Nat.totient q : ℝ) * |psiAP x q a - x / (Nat.totient q : ℝ)| := by
      field_simp [hx_pos.ne']
    linarith
  -- 1. Bound `x * bmorW q x`
  have hW_bnd : x * bmorW q x ≤ (Nat.totient q : ℝ) * (25 * Real.log x + 62) :=
    mul_bmorW_le (by omega) (hqQ.trans hQ) hx1
  -- 2. Bound `x * bmorV q r x τ H` via `bmor_low_zero_sum_le_cap`
  have hV_bnd : x * bmorV q r x τ H ≤
      (Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) H * (1 + (r : ℝ) * τ / 2) * Real.sqrt x := by
    unfold bmorV
    have hchar_V : ∀ χ : DirichletCharacter ℂ q,
        (∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖)) ≤
          bmorLowZeroCap (Q : ℝ) H * x ^ (-1 / 2 : ℝ) := by
      intro χ
      have hdQ : (χ.conductor : ℝ) ≤ (Q : ℝ) := by
        exact_mod_cast (Nat.le_of_dvd (by omega) χ.conductor_dvd_level).trans hqQ
      have hterm_eq : (∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖)) =
          x ^ (-1 / 2 : ℝ) * ∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hm := (mem_bmorCriticalZerosUpTo χ H ρ).mp hρ
        have hre : ρ.re = 1 / 2 := hgrh_H χ ρ hm.1 hm.2
        have hr1 : ρ.re - 1 = (-1 / 2 : ℝ) := by linarith
        rw [hr1]
        ring
      rw [hterm_eq, mul_comm]
      exact mul_le_mul_of_nonneg_right (bmor_low_zero_sum_le_cap pub.prop2_5 χ hdQ hH1 (hgrh_H χ))
        (Real.rpow_pos_of_pos hx_pos _).le
    have hsum_V : (∑ χ : DirichletCharacter ℂ q,
        ∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖)) ≤
        (Nat.totient q : ℝ) * (bmorLowZeroCap (Q : ℝ) H * x ^ (-1 / 2 : ℝ)) := by
      calc
        (∑ χ : DirichletCharacter ℂ q,
            ∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖))
          ≤ ∑ _χ : DirichletCharacter ℂ q, (bmorLowZeroCap (Q : ℝ) H * x ^ (-1 / 2 : ℝ)) :=
            Finset.sum_le_sum fun χ _ => hchar_V χ
        _ = (Nat.totient q : ℝ) * (bmorLowZeroCap (Q : ℝ) H * x ^ (-1 / 2 : ℝ)) := by
            simp [card_dirichletCharacter_eq_totient q]
    have hx_sqrt : x * x ^ (-1 / 2 : ℝ) = Real.sqrt x := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx_pos.le (by norm_num)]
      norm_num
    have h1rτ_pos : 0 ≤ 1 + (r : ℝ) * τ / 2 := by positivity
    calc
      x * ((1 + (r : ℝ) * τ / 2) * ∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ bmorCriticalZerosUpTo χ H, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖))
        ≤ x * ((1 + (r : ℝ) * τ / 2) *
            ((Nat.totient q : ℝ) * (bmorLowZeroCap (Q : ℝ) H * x ^ (-1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_V h1rτ_pos) hx_pos.le
      _ = (Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) H * (1 + (r : ℝ) * τ / 2) *
            (x * x ^ (-1 / 2 : ℝ)) := by ring
      _ = (Nat.totient q : ℝ) * bmorLowZeroCap (Q : ℝ) H * (1 + (r : ℝ) * τ / 2) * Real.sqrt x := by
          rw [hx_sqrt]
  -- 3. Bound `bmorU q r x τ H` via functional-equation pairing + `BMORProp4_34` + `bmor_high_zero_power_sum_le`
  have hU_bnd : bmorU q r x τ H ≤
      bmorSmoothFactor r τ * bmorHighZeroSum (Q : ℝ) (Nat.totient q : ℝ) z r := by
    unfold bmorU
    have hsmooth_nonneg : 0 ≤ bmorSmoothFactor r τ := by
      unfold bmorSmoothFactor
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
    apply mul_le_mul_of_nonneg_left _ hsmooth_nonneg
    let lam := Real.log (10 ^ 8 : ℝ)
    let ar := (r : ℝ) - z / (bmorZeroFreeR * lam ^ 2)
    let Br := (lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (bmorC1 * lam + bmorC2) / H
    let Br0 := (lam / (r : ℝ) + 1 / (r : ℝ) ^ 2) / Real.pi + 2 * (bmorC1 * lam + bmorC2) / H
    let C_char : ℝ := (1 / (2 * H ^ r)) *
      (Real.exp (-z / (bmorZeroFreeR * lam)) * Br + Real.exp (-z / 2) * Br0)
    have hchar_U : ∀ χ : DirichletCharacter ℂ q,
        (∑' ρ : ℂ, bmorUTerm χ r x H ρ) ≤ C_char := by
      intro χ
      have hdQ : (χ.conductor : ℝ) ≤ (Q : ℝ) := by
        exact_mod_cast (Nat.le_of_dvd (by omega) χ.conductor_dvd_level).trans hqQ
      refine (bmorUTerm_summable_and_tsum_le χ r hx_pos fun T hHT => ?_).2
      let S := (bmorCriticalZerosUpTo χ T).filter (fun ρ => H < |ρ.im|)
      -- Step 3a: bound denominator by `|ρ.im| ^ (r + 1)`
      have hden_step : (∑ ρ ∈ S, bmorUTerm χ r x H ρ) ≤
          ∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / |ρ.im| ^ (r + 1)) := by
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have him_gt : H < |ρ.im| := (Finset.mem_filter.mp hρ).2
        have him_pos : 0 < |ρ.im| := by linarith
        rw [bmorUTerm, if_pos him_gt]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hx_pos _).le
          (pow_pos him_pos _) (prod_norm_add_ge_abs_im_pow ρ r)
      -- Step 3b: pair `ρ` with `1 - star ρ` on `S`
      have hinv_symm : (∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / |ρ.im| ^ (r + 1))) =
          ∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * (x ^ (-ρ.re) / |ρ.im| ^ (r + 1)) := by
        symm
        refine Finset.sum_bij (fun ρ _ => 1 - star ρ) ?_ ?_ ?_ ?_
        · intro ρ hρ
          have hm1 := Finset.mem_filter.mp hρ
          have hm2 := (mem_bmorCriticalZerosUpTo χ T ρ).mp hm1.1
          have hcrit' : bmorIsCriticalZero χ (1 - star ρ) := by
            rw [← bmorZeroMult_pos_iff, bmorZeroMult_one_sub_star, bmorZeroMult_pos_iff]
            exact hm2.1
          have him_eq : |(1 - star ρ).im| = |ρ.im| := by simp
          rw [Finset.mem_filter, mem_bmorCriticalZerosUpTo, him_eq]
          exact ⟨⟨hcrit', hm2.2⟩, hm1.2⟩
        · intro ρ₁ _ ρ₂ _ heq
          have := congrArg (fun w : ℂ => star (1 - w)) heq
          simpa [star_star] using this
        · intro ρ hρ
          refine ⟨1 - star ρ, ?_, by simp [star_sub]⟩
          have hm1 := Finset.mem_filter.mp hρ
          have hm2 := (mem_bmorCriticalZerosUpTo χ T ρ).mp hm1.1
          have hcrit' : bmorIsCriticalZero χ (1 - star ρ) := by
            rw [← bmorZeroMult_pos_iff, bmorZeroMult_one_sub_star, bmorZeroMult_pos_iff]
            exact hm2.1
          have him_eq : |(1 - star ρ).im| = |ρ.im| := by simp
          rw [Finset.mem_filter, mem_bmorCriticalZerosUpTo, him_eq]
          exact ⟨⟨hcrit', hm2.2⟩, hm1.2⟩
        · intro ρ _
          have him_eq : |(1 - star ρ).im| = |ρ.im| := by simp
          have hre_eq : (1 - star ρ).re - 1 = -ρ.re := by simp
          rw [bmorZeroMult_one_sub_star, him_eq, hre_eq]
      have havg : (∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / |ρ.im| ^ (r + 1))) =
          (1 / 2 : ℝ) * ∑ ρ ∈ S,
            (bmorZeroMult χ ρ : ℝ) * ((x ^ (ρ.re - 1) + x ^ (-ρ.re)) / |ρ.im| ^ (r + 1)) := by
        have hadd : (∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / |ρ.im| ^ (r + 1))) +
            (∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * (x ^ (-ρ.re) / |ρ.im| ^ (r + 1))) =
            ∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * ((x ^ (ρ.re - 1) + x ^ (-ρ.re)) / |ρ.im| ^ (r + 1)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun ρ _ => ?_; ring
        linarith [hinv_symm, hadd]
      -- Step 3c: zero-free region `η ≤ ρ.re ≤ 1 - η` and `x^(β-1) + x^(-β) ≤ exp(-z / (R * log(Q*|γ|))) + exp(-z/2)`
      have hzf_zero : ∀ σ : ℂ, bmorIsCriticalZero χ σ → H < |σ.im| →
          σ.re ≤ 1 - 1 / (bmorZeroFreeR * Real.log ((Q : ℝ) * |σ.im|)) := by
        intro σ hcrit_σ him_σ
        have hQ_im_gt : (10 ^ 8 : ℝ) < (Q : ℝ) * |σ.im| := by
          have : (Q : ℝ) * H = 10 ^ 8 := by dsimp [H]; field_simp [hQ_pos.ne']
          nlinarith
        have hlog_Q_im_gt2 : 2 < Real.log ((Q : ℝ) * |σ.im|) := by
          have hexp2 : Real.exp 2 < (10 ^ 8 : ℝ) := by
            have he3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
            have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
              rw [← Real.exp_add]; norm_num
            nlinarith [Real.exp_pos 1]
          rw [← Real.log_exp 2]
          exact Real.log_lt_log (Real.exp_pos 2) (hexp2.trans hQ_im_gt)
        have hR_pos : (2 : ℝ) < bmorZeroFreeR := by unfold bmorZeroFreeR; norm_num
        rcases pub.prop4_34 q χ σ (hqQ.trans hQ) hcrit_σ with ⟨_, hhalf⟩ | ⟨_, hzf⟩
        · rw [hhalf]
          have hden_gt2 : 2 < bmorZeroFreeR * Real.log ((Q : ℝ) * |σ.im|) := by nlinarith
          have h12 : 1 / (bmorZeroFreeR * Real.log ((Q : ℝ) * |σ.im|)) ≤ 1 / 2 :=
            one_div_le_one_div_of_le (by norm_num) hden_gt2.le
          linarith
        · refine hzf.trans ?_
          have hd_pos : (0 : ℝ) < (χ.conductor : ℝ) :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero)
          have hd_im_gt1 : 1 < (χ.conductor : ℝ) * |σ.im| := by
            have hd1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
              exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
            nlinarith
          have hlog_pos : 0 < Real.log ((χ.conductor : ℝ) * |σ.im|) := Real.log_pos hd_im_gt1
          have hlog_le : Real.log ((χ.conductor : ℝ) * |σ.im|) ≤ Real.log ((Q : ℝ) * |σ.im|) :=
            Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hdQ (abs_nonneg _))
          have hinv : 1 / (bmorZeroFreeR * Real.log ((Q : ℝ) * |σ.im|)) ≤
              1 / (bmorZeroFreeR * Real.log ((χ.conductor : ℝ) * |σ.im|)) :=
            one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hlog_le (by linarith))
          linarith
      -- Pointwise bound on summand into the two power-weighted series
      have hterm_dom : ∀ ρ ∈ S,
          (x ^ (ρ.re - 1) + x ^ (-ρ.re)) / |ρ.im| ^ (r + 1) ≤
            Real.exp (-z / (bmorZeroFreeR * lam)) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-ar - 1)) +
            Real.exp (-z / 2) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-(r : ℝ) - 1)) := by
        intro ρ hρ
        have hm1 := Finset.mem_filter.mp hρ
        have hcrit := ((mem_bmorCriticalZerosUpTo χ T ρ).mp hm1.1).1
        have him_gt : H < |ρ.im| := hm1.2
        have him_pos : 0 < |ρ.im| := by linarith
        have hH_pos : 0 < H := by linarith
        let η : ℝ := 1 / (bmorZeroFreeR * Real.log ((Q : ℝ) * |ρ.im|))
        have hβ_hi : ρ.re ≤ 1 - η := hzf_zero ρ hcrit him_gt
        have hcrit_symm : bmorIsCriticalZero χ (1 - star ρ) := by
          rw [← bmorZeroMult_pos_iff, bmorZeroMult_one_sub_star, bmorZeroMult_pos_iff]
          exact hcrit
        have hβ_lo : η ≤ ρ.re := by
          have hsym := hzf_zero (1 - star ρ) hcrit_symm (by simpa using him_gt)
          have hre_sym : (1 - star ρ).re = 1 - ρ.re := by simp
          have him_sym : |(1 - star ρ).im| = |ρ.im| := by simp
          rw [hre_sym, him_sym] at hsym
          linarith
        have hsum_rpow : x ^ (ρ.re - 1) + x ^ (-ρ.re) ≤ x ^ (-η) + x ^ (-1 / 2 : ℝ) := by
          rcases le_or_gt (1 / 2 : ℝ) ρ.re with hge | hlt
          · have h1 : x ^ (ρ.re - 1) ≤ x ^ (-η) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
            have h2 : x ^ (-ρ.re) ≤ x ^ (-1 / 2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
            linarith
          · have h1 : x ^ (ρ.re - 1) ≤ x ^ (-1 / 2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
            have h2 : x ^ (-ρ.re) ≤ x ^ (-η) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
            linarith
        have hQH_eq : (Q : ℝ) * H = 10 ^ 8 := by dsimp [H]; field_simp [hQ_pos.ne']
        have hlam_pos : 0 < lam := Real.log_pos (by norm_num)
        have hs_pos : 0 < Real.log (|ρ.im| / H) := Real.log_pos ((one_lt_div hH_pos).mpr him_gt)
        have hlog_Qim : Real.log ((Q : ℝ) * |ρ.im|) = lam + Real.log (|ρ.im| / H) := by
          have heq : (Q : ℝ) * |ρ.im| = (10 ^ 8 : ℝ) * (|ρ.im| / H) := by
            rw [← hQH_eq]; field_simp [hH_pos.ne']
          rw [heq, Real.log_mul (by norm_num) (div_pos him_pos hH_pos).ne']
        have hη_pos : 0 < η := by
          dsimp [η]; rw [hlog_Qim]; unfold bmorZeroFreeR; positivity
        have hx_η : x ^ (-η) ≤ Real.exp (-z * η) := by
          rw [Real.rpow_def_of_pos hx_pos]
          exact Real.exp_le_exp.mpr (by nlinarith)
        have hx_half : x ^ (-1 / 2 : ℝ) ≤ Real.exp (-z / 2) := by
          rw [Real.rpow_def_of_pos hx_pos]
          exact Real.exp_le_exp.mpr (by linarith)
        -- Linearize `-z * η = -z / (R * (lam + s)) ≤ -z / (R * lam) + z * s / (R * lam^2)`
        have hlin_exp : -z * η ≤ -z / (bmorZeroFreeR * lam) +
            (z / (bmorZeroFreeR * lam ^ 2)) * Real.log (|ρ.im| / H) := by
          dsimp [η]
          rw [hlog_Qim]
          let s := Real.log (|ρ.im| / H)
          have hR_pos : 0 < bmorZeroFreeR := by unfold bmorZeroFreeR; norm_num
          have hden1 : 0 < bmorZeroFreeR * (lam + s) := by positivity
          have hden2 : 0 < bmorZeroFreeR * lam ^ 2 := by positivity
          rw [show -z * (1 / (bmorZeroFreeR * (lam + s))) = -z / (bmorZeroFreeR * (lam + s)) by ring]
          rw [show -z / (bmorZeroFreeR * lam) + z / (bmorZeroFreeR * lam ^ 2) * s =
              (-z * lam + z * s) / (bmorZeroFreeR * lam ^ 2) by
            field_simp [hR_pos.ne', hlam_pos.ne'] ]
          rw [div_le_div_iff₀ hden1 hden2]
          have hz_nonneg : 0 ≤ z := by linarith
          nlinarith [mul_nonneg hz_nonneg (sq_nonneg s)]
        have hexp_η : Real.exp (-z * η) ≤
            Real.exp (-z / (bmorZeroFreeR * lam)) * (|ρ.im| / H) ^ (z / (bmorZeroFreeR * lam ^ 2)) := by
          calc
            Real.exp (-z * η)
              ≤ Real.exp (-z / (bmorZeroFreeR * lam) +
                  (z / (bmorZeroFreeR * lam ^ 2)) * Real.log (|ρ.im| / H)) :=
                Real.exp_le_exp.mpr hlin_exp
            _ = Real.exp (-z / (bmorZeroFreeR * lam)) *
                Real.exp ((z / (bmorZeroFreeR * lam ^ 2)) * Real.log (|ρ.im| / H)) :=
                Real.exp_add _ _
            _ = Real.exp (-z / (bmorZeroFreeR * lam)) *
                (|ρ.im| / H) ^ (z / (bmorZeroFreeR * lam ^ 2)) := by
                rw [Real.rpow_def_of_pos (div_pos him_pos hH_pos), mul_comm (Real.log _)]
        have hpow_inv : (|ρ.im| ^ (r + 1))⁻¹ = (H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-(r : ℝ) - 1) := by
          have hexp : -(r : ℝ) - 1 = -(((r + 1 : ℕ) : ℝ)) := by push_cast; ring
          rw [hexp, Real.rpow_neg (div_pos him_pos hH_pos).le, Real.rpow_natCast,
            div_pow |ρ.im| H (r + 1), inv_div,
            div_eq_mul_inv, inv_mul_cancel_left₀ (pow_ne_zero _ hH_pos.ne')]
        have hpow_ar : (|ρ.im| / H) ^ (z / (bmorZeroFreeR * lam ^ 2)) * (|ρ.im| / H) ^ (-(r : ℝ) - 1) =
            (|ρ.im| / H) ^ (-ar - 1) := by
          rw [← Real.rpow_add (div_pos him_pos hH_pos)]
          congr 1; dsimp [ar]; ring
        calc
          (x ^ (ρ.re - 1) + x ^ (-ρ.re)) / |ρ.im| ^ (r + 1)
            ≤ (Real.exp (-z / (bmorZeroFreeR * lam)) * (|ρ.im| / H) ^ (z / (bmorZeroFreeR * lam ^ 2)) +
                Real.exp (-z / 2)) * (|ρ.im| ^ (r + 1))⁻¹ := by
              rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right
                (hsum_rpow.trans (add_le_add (hx_η.trans hexp_η) hx_half)) (by positivity)
          _ = Real.exp (-z / (bmorZeroFreeR * lam)) *
                ((H ^ (r + 1))⁻¹ * ((|ρ.im| / H) ^ (z / (bmorZeroFreeR * lam ^ 2)) *
                  (|ρ.im| / H) ^ (-(r : ℝ) - 1))) +
              Real.exp (-z / 2) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-(r : ℝ) - 1)) := by
              rw [hpow_inv]; ring
          _ = Real.exp (-z / (bmorZeroFreeR * lam)) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-ar - 1)) +
              Real.exp (-z / 2) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-(r : ℝ) - 1)) := by
              rw [hpow_ar]
      have hQH_log : Real.log ((Q : ℝ) * H) ≤ lam := by
        have hQH_eq : (Q : ℝ) * H = 10 ^ 8 := by dsimp [H]; field_simp [hQ_pos.ne']
        rw [hQH_eq]
      have hb1 := bmor_high_zero_power_sum_le pub.prop2_5 χ hdQ hH1000 hHT hQH_log (r := r) har
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
      have hb2 := bmor_high_zero_power_sum_le pub.prop2_5 χ hdQ hH1000 hHT hQH_log (r := r) hr_pos
      have hsum_dom : (∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) *
          ((x ^ (ρ.re - 1) + x ^ (-ρ.re)) / |ρ.im| ^ (r + 1))) ≤
          Real.exp (-z / (bmorZeroFreeR * lam)) * ((H ^ r)⁻¹ * Br) +
          Real.exp (-z / 2) * ((H ^ r)⁻¹ * Br0) := by
        calc
          (∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * ((x ^ (ρ.re - 1) + x ^ (-ρ.re)) / |ρ.im| ^ (r + 1)))
            ≤ ∑ ρ ∈ S, ((bmorZeroMult χ ρ : ℝ) *
                (Real.exp (-z / (bmorZeroFreeR * lam)) *
                  ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-ar - 1)) +
                Real.exp (-z / 2) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-(r : ℝ) - 1)))) :=
              Finset.sum_le_sum fun ρ hρ => mul_le_mul_of_nonneg_left (hterm_dom ρ hρ) (Nat.cast_nonneg _)
          _ = Real.exp (-z / (bmorZeroFreeR * lam)) *
                (∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-ar - 1))) +
              Real.exp (-z / 2) *
                (∑ ρ ∈ S, (bmorZeroMult χ ρ : ℝ) * ((H ^ (r + 1))⁻¹ * (|ρ.im| / H) ^ (-(r : ℝ) - 1))) := by
              simp only [mul_add, Finset.sum_add_distrib]
              congr 1 <;> (rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring)
          _ ≤ Real.exp (-z / (bmorZeroFreeR * lam)) * ((H ^ r)⁻¹ * Br) +
              Real.exp (-z / 2) * ((H ^ r)⁻¹ * Br0) :=
              add_le_add
                (mul_le_mul_of_nonneg_left hb1 (Real.exp_pos _).le)
                (mul_le_mul_of_nonneg_left hb2 (Real.exp_pos _).le)
      have hC_eq : (1 / 2 : ℝ) *
          (Real.exp (-z / (bmorZeroFreeR * lam)) * ((H ^ r)⁻¹ * Br) +
           Real.exp (-z / 2) * ((H ^ r)⁻¹ * Br0)) = C_char := by
        dsimp [C_char]; ring
      linarith [hden_step, havg, hsum_dom, hC_eq]
    calc
      (∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, bmorUTerm χ r x H ρ)
        ≤ ∑ _χ : DirichletCharacter ℂ q, C_char := Finset.sum_le_sum fun χ _ => hchar_U χ
      _ = (Nat.totient q : ℝ) * C_char := by simp [card_dirichletCharacter_eq_totient q]
      _ = bmorHighZeroSum (Q : ℝ) (Nat.totient q : ℝ) z r := by
          unfold bmorHighZeroSum; dsimp [C_char, H, lam, ar, Br, Br0]; ring
  have hU_mul : (bmorU q r x τ H + (r : ℝ) * τ / 2) * x ≤
      ((r : ℝ) * τ / 2 + bmorSmoothFactor r τ * bmorHighZeroSum (Q : ℝ) (Nat.totient q : ℝ) z r) * x :=
    mul_le_mul_of_nonneg_right (by linarith) hx_pos.le
  dsimp [H] at hexp_mul hU_mul hV_bnd
  linarith [hexp_mul, hU_mul, hV_bnd, hW_bnd]

/-- Proof of `BMORSmoothedPsiModTwo` from verbatim `BMORPublishedExplicitFormula`. -/
theorem bmorSmoothedPsiModTwo_of_published (pub : BMORPublishedExplicitFormula) :
    BMORSmoothedPsiModTwo := by
  intro rs Hs τs zs x hrs hHs_lo hHs_hi hlogHs hτs hrsτs hzs hx1 hlog
  have : NeZero 2 := ⟨by decide⟩
  obtain ⟨hx2, hτs_dom⟩ := smoothing_domain_of_log_ge_14 hx1 (hzs.trans hlog) hrs hτs hrsτs
  have hx_pos : 0 < x := by linarith
  have hHs1 : 1 ≤ Hs := by linarith
  have hcop2 : Nat.Coprime 2 (1 : ℤ).natAbs := by decide
  have htot2 : (Nat.totient 2 : ℝ) = 1 := by exact_mod_cast (by decide : Nat.totient 2 = 1)
  -- Every `χ : DirichletCharacter ℂ 2` has conductor `1` (since `φ(2) = 1`, `χ = 1`)
  have hcond_eq1 : ∀ χ : DirichletCharacter ℂ 2, χ.conductor = 1 := by
    intro χ
    have hcard : Fintype.card (DirichletCharacter ℂ 2) = 1 := by
      rw [card_dirichletCharacter_eq_totient 2]; decide
    have hsub : Subsingleton (DirichletCharacter ℂ 2) := Fintype.card_le_one_iff_subsingleton.mp hcard.le
    rw [Subsingleton.elim χ 1]
    exact DirichletCharacter.conductor_one
  have hgrh_Hs : ∀ χ : DirichletCharacter ℂ 2, bmorSatisfiesGRH χ Hs := by
    intro χ
    let d := χ.conductor
    have : NeZero d := ⟨χ.conductor_ne_zero⟩
    have hd1 : d = 1 := hcond_eq1 χ
    have hprim := pub.prop2_7 d χ.primitiveCharacter χ.primitiveCharacter_isPrimitive (by omega)
    have hver : bmorVerifiedHeight d = 30610046000 := by unfold bmorVerifiedHeight; simp [hd1]
    exact bmorSatisfiesGRH_of_primitive χ fun ρ hρ him =>
      hprim ρ hρ (by rw [hver]; exact him.trans hHs_hi)
  have hgrh_1 : ∀ χ : DirichletCharacter ℂ 2, bmorSatisfiesGRH χ 1 :=
    fun χ ρ hρ him => hgrh_Hs χ ρ hρ (him.trans hHs1)
  have hexp_formula := (pub.prop2_1 2 1 rs x τs Hs hcop2 hx2 hHs1 hrs hτs hτs_dom hgrh_1).le
  rw [chebyshevPsiAP_eq_psiAP hx2.le 2 1, htot2, div_one] at hexp_formula
  have hexp_mul : |psiAP x 2 1 - x| ≤
      (bmorU 2 rs x τs Hs + (rs : ℝ) * τs / 2) * x + x * bmorV 2 rs x τs Hs + x * bmorW 2 x := by
    have h := mul_le_mul_of_nonneg_left hexp_formula hx_pos.le
    have hlhs : x * ((1 / x) * |psiAP x 2 1 - x|) = |psiAP x 2 1 - x| := by
      field_simp [hx_pos.ne']
    linarith
  have hW_bnd : x * bmorW 2 x ≤ 25 * Real.log x + 62 := by
    simpa [htot2] using mul_bmorW_le (q := 2) (by decide) (by decide) hx1
  have hV_bnd : x * bmorV 2 rs x τs Hs ≤
      bmorLowZeroCap 2 Hs * (1 + (rs : ℝ) * τs / 2) * Real.sqrt x := by
    unfold bmorV
    have hchar_V : ∀ χ : DirichletCharacter ℂ 2,
        (∑ ρ ∈ bmorCriticalZerosUpTo χ Hs, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖)) ≤
          bmorLowZeroCap 2 Hs * x ^ (-1 / 2 : ℝ) := by
      intro χ
      have hd2 : (χ.conductor : ℝ) ≤ 2 := by rw [hcond_eq1 χ]; norm_num
      have hterm_eq : (∑ ρ ∈ bmorCriticalZerosUpTo χ Hs, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖)) =
          x ^ (-1 / 2 : ℝ) * ∑ ρ ∈ bmorCriticalZerosUpTo χ Hs, (bmorZeroMult χ ρ : ℝ) * (1 / ‖ρ‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hm := (mem_bmorCriticalZerosUpTo χ Hs ρ).mp hρ
        have hre : ρ.re = 1 / 2 := hgrh_Hs χ ρ hm.1 hm.2
        have hr1 : ρ.re - 1 = (-1 / 2 : ℝ) := by linarith
        rw [hr1]; ring
      rw [hterm_eq, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (bmor_low_zero_sum_le_cap pub.prop2_5 χ hd2 hHs1 (hgrh_Hs χ))
        (Real.rpow_pos_of_pos hx_pos _).le
    have hsum_V : (∑ χ : DirichletCharacter ℂ 2,
        ∑ ρ ∈ bmorCriticalZerosUpTo χ Hs, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖)) ≤
        bmorLowZeroCap 2 Hs * x ^ (-1 / 2 : ℝ) := by
      calc
        (∑ χ : DirichletCharacter ℂ 2,
            ∑ ρ ∈ bmorCriticalZerosUpTo χ Hs, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖))
          ≤ ∑ _χ : DirichletCharacter ℂ 2, (bmorLowZeroCap 2 Hs * x ^ (-1 / 2 : ℝ)) :=
            Finset.sum_le_sum fun χ _ => hchar_V χ
        _ = bmorLowZeroCap 2 Hs * x ^ (-1 / 2 : ℝ) := by
            simp [card_dirichletCharacter_eq_totient 2]
    have hx_sqrt : x * x ^ (-1 / 2 : ℝ) = Real.sqrt x := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx_pos.le (by norm_num)]
      norm_num
    calc
      x * ((1 + (rs : ℝ) * τs / 2) * ∑ χ : DirichletCharacter ℂ 2,
          ∑ ρ ∈ bmorCriticalZerosUpTo χ Hs, (bmorZeroMult χ ρ : ℝ) * (x ^ (ρ.re - 1) / ‖ρ‖))
        ≤ x * ((1 + (rs : ℝ) * τs / 2) * (bmorLowZeroCap 2 Hs * x ^ (-1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_V (by positivity)) hx_pos.le
      _ = bmorLowZeroCap 2 Hs * (1 + (rs : ℝ) * τs / 2) * (x * x ^ (-1 / 2 : ℝ)) := by ring
      _ = bmorLowZeroCap 2 Hs * (1 + (rs : ℝ) * τs / 2) * Real.sqrt x := by rw [hx_sqrt]
  -- Bound `bmorU 2 rs x τs Hs` using `x^(β - 1) ≤ 1` + `bmor_high_zero_power_sum_le` (`Q = 2, Λ₀ = 25`)
  have hU_bnd : bmorU 2 rs x τs Hs ≤ bmorSmoothFactor rs τs * bmorParityHighZeroSum Hs rs := by
    unfold bmorU
    have hsmooth_nonneg : 0 ≤ bmorSmoothFactor rs τs := by
      unfold bmorSmoothFactor
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
    apply mul_le_mul_of_nonneg_left _ hsmooth_nonneg
    have hchar_U : ∀ χ : DirichletCharacter ℂ 2,
        (∑' ρ : ℂ, bmorUTerm χ rs x Hs ρ) ≤ bmorParityHighZeroSum Hs rs := by
      intro χ
      have hd2 : (χ.conductor : ℝ) ≤ 2 := by rw [hcond_eq1 χ]; norm_num
      have hrs_pos : (0 : ℝ) < (rs : ℝ) := by exact_mod_cast hrs
      refine (bmorUTerm_summable_and_tsum_le χ rs hx_pos fun T hHsT => ?_).2
      have hterm_le : ∀ ρ ∈ (bmorCriticalZerosUpTo χ T).filter (fun ρ => Hs < |ρ.im|),
          bmorUTerm χ rs x Hs ρ ≤
            (bmorZeroMult χ ρ : ℝ) * ((Hs ^ (rs + 1))⁻¹ * (|ρ.im| / Hs) ^ (-(rs : ℝ) - 1)) := by
        intro ρ hρ
        have hm1 := Finset.mem_filter.mp hρ
        have hcrit := ((mem_bmorCriticalZerosUpTo χ T ρ).mp hm1.1).1
        have him_gt : Hs < |ρ.im| := hm1.2
        have him_pos : 0 < |ρ.im| := by linarith
        have hHs_pos : 0 < Hs := by linarith
        rw [bmorUTerm, if_pos him_gt]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hx_le1 : x ^ (ρ.re - 1) ≤ 1 := by
          calc
            x ^ (ρ.re - 1) ≤ x ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hcrit.2.1])
            _ = 1 := Real.rpow_zero x
        have hden := prod_norm_add_ge_abs_im_pow ρ rs
        have hquot : x ^ (ρ.re - 1) / (∏ j ∈ Finset.range (rs + 1), ‖ρ + (j : ℂ)‖) ≤
            (|ρ.im| ^ (rs + 1))⁻¹ := by
          calc
            x ^ (ρ.re - 1) / (∏ j ∈ Finset.range (rs + 1), ‖ρ + (j : ℂ)‖)
              ≤ 1 / (∏ j ∈ Finset.range (rs + 1), ‖ρ + (j : ℂ)‖) :=
                div_le_div_of_nonneg_right hx_le1 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            _ ≤ 1 / |ρ.im| ^ (rs + 1) := one_div_le_one_div_of_le (pow_pos him_pos _) hden
            _ = (|ρ.im| ^ (rs + 1))⁻¹ := one_div _
        have hpow_eq : (|ρ.im| ^ (rs + 1))⁻¹ =
            (Hs ^ (rs + 1))⁻¹ * (|ρ.im| / Hs) ^ (-(rs : ℝ) - 1) := by
          have hexp : -(rs : ℝ) - 1 = -(((rs + 1 : ℕ) : ℝ)) := by push_cast; ring
          rw [hexp, Real.rpow_neg (div_pos him_pos hHs_pos).le, Real.rpow_natCast, div_pow, inv_div,
            div_eq_mul_inv, inv_mul_cancel_left₀ (pow_ne_zero _ hHs_pos.ne')]
        exact hquot.trans_eq hpow_eq
      have hb := bmor_high_zero_power_sum_le pub.prop2_5 χ hd2 hHs_lo hHsT hlogHs
        (r := rs) hrs_pos
      refine (Finset.sum_le_sum hterm_le).trans (hb.trans_eq ?_)
      unfold bmorParityHighZeroSum
      ring
    calc
      (∑ χ : DirichletCharacter ℂ 2, ∑' ρ : ℂ, bmorUTerm χ rs x Hs ρ)
        ≤ ∑ _χ : DirichletCharacter ℂ 2, bmorParityHighZeroSum Hs rs :=
          Finset.sum_le_sum fun χ _ => hchar_U χ
      _ = bmorParityHighZeroSum Hs rs := by simp [card_dirichletCharacter_eq_totient 2]
  have hU_mul : (bmorU 2 rs x τs Hs + (rs : ℝ) * τs / 2) * x ≤
      ((rs : ℝ) * τs / 2 + bmorSmoothFactor rs τs * bmorParityHighZeroSum Hs rs) * x :=
    mul_le_mul_of_nonneg_right (by linarith) hx_pos.le
  linarith [hexp_mul, hU_mul, hV_bnd, hW_bnd]

/-- **Main Trust-Boundary Theorem**:
    `BMORExplicitFormulaImports` is completely proved in Lean from the four verbatim
    published BMOR (2018) Propositions 2.1, 2.5, 2.7, and 4.34 (`BMORPublishedExplicitFormula`)
    together with Rosser–Schoenfeld (1962) Theorem 4 `(3.15)` (`RSThetaUpper`). -/
theorem bmorExplicitFormulaImports_of_published
    (pub : BMORPublishedExplicitFormula) (rs_theta : RSThetaUpper) :
    BMORExplicitFormulaImports where
  rs_theta_upper := rs_theta
  smoothed_psi_small_moduli := bmorSmoothedPsiSmallModuli_of_published pub
  smoothed_psi_mod_two := bmorSmoothedPsiModTwo_of_published pub

end

end Sude
