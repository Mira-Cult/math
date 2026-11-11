import Sude.FC2KSubbandCore
import Sude.FC2KPoolMeanBounds

/-!
# Parametric Rational Sub-Band Discharge Engine (`FC2KSubbandDischarge`)

Reduces all hypotheses of `fc2k_subband_hasSquare` on any sub-band `[n_lo, n_hi]`
(`2001 ≤ n_lo ≤ n ≤ n_hi ≤ 19483`, `Odd n`) to a single computable `Bool` check
`checkFC2KSubbandSpec` over `ℚ` and `ℕ`, verified per sub-band via `decide +kernel`.
-/

namespace Sude

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Computable window-cap witness for `evalWindowWitness`. -/
inductive FC2KWindowWitness where
  | aboveMaxHi
  | wordCap (idx tiles sliver : ℕ)
  | octCap (idx tiles sliver : ℕ)
  deriving DecidableEq, Repr

/-- Per-stage bridge witness `(M_j, w_low, w_high)`. -/
structure FC2KBridgeStageSpec where
  M : ℕ
  wLow : FC2KWindowWitness
  wHigh : FC2KWindowWitness
  deriving DecidableEq, Repr

/-- Complete rational/integer parameter bundle for a single FC2K sub-band `[n_lo, n_hi]`. -/
structure FC2KSubbandSpec where
  n_lo : ℕ
  n_hi : ℕ
  J_max : ℕ
  W_ord : ℕ
  W_diag : ℕ
  N_bins : ℕ
  δ : ℚ
  ε : ℚ
  c_lo : ℚ
  c_hi : ℚ
  a_X : ℕ
  S_lo_up : ℕ
  X_lo : ℕ
  b_X : ℕ
  a_Xh : ℕ
  S_hi_up : ℕ
  X_hi : ℕ
  S_lo : ℕ
  c_W : ℚ
  c_N : ℚ
  c_B : ℚ
  brStages : List FC2KBridgeStageSpec
  wHalf : FC2KWindowWitness
  wFull : FC2KWindowWitness
  deriving DecidableEq, Repr

def fc2kLn2Lo : ℚ := 6931471803 / 10000000000
def fc2kLn2Hi : ℚ := 6931471808 / 10000000000

def bgLiLowerNormQ (u : ℚ) : ℚ :=
  1 / u + 1 / u ^ 2 + 2 / u ^ 3 + 6 / u ^ 4

def bgLiUpperNormQ (u : ℚ) : ℚ :=
  1 / u + 1 / u ^ 2 + 4 / u ^ 3

def fc2kBridgeRatioLo (P X_hi : ℕ) : ℕ → ℚ
  | 0 => ((2 ^ (P + 1) - 2 : ℕ) : ℚ) / (X_hi : ℚ)
  | j + 1 =>
      let r := fc2kBridgeRatioLo P X_hi j
      r + (94 / 100 : ℚ) * min r (1 / 2)

def fc2kBridgeRatioHi (P X_lo : ℕ) : ℕ → ℚ
  | 0 => ((2 ^ (P + 1) - 2 : ℕ) : ℚ) / (X_lo : ℚ)
  | j + 1 =>
      let s := fc2kBridgeRatioHi P X_lo j
      s + (94 / 100 : ℚ) * min s (1 / 2)

def fc2kSliverCap (sliver : ℕ) : ℕ :=
  if sliver = 0 then 0 else 2 * (sliver / 6 + 2)

/-- Computable window-cap evaluator over `ℚ` and `ℕ`. -/
def evalWindowWitness (corrLo maxHi : ℕ)
    (windowCaps octWindowCaps : List PrefixWindowCap)
    (lo_min width_max : ℚ) : FC2KWindowWitness → Option ℕ
  | .aboveMaxHi =>
      if (maxHi : ℚ) ≤ lo_min then some 0 else none
  | .wordCap idx tiles sliver =>
      match windowCaps[idx]? with
      | none => none
      | some wc =>
          let m_start := corrLo + 49152 * wc.minWordIdx
          let B := tiles * ((wc.spanWords - 1) * 49152)
          if 2 ≤ wc.spanWords ∧ (m_start : ℚ) - (sliver : ℚ) ≤ lo_min ∧
              width_max + 1 ≤ (B : ℚ) then
            some (fc2kSliverCap sliver + tiles * wc.cap)
          else
            none
  | .octCap idx tiles sliver =>
      match octWindowCaps[idx]? with
      | none => none
      | some wc =>
          let m_start := corrLo + 393216 * wc.minWordIdx
          let B := tiles * ((wc.spanWords - 1) * 393216)
          if 2 ≤ wc.spanWords ∧ (m_start : ℚ) - (sliver : ℚ) ≤ lo_min ∧
              width_max + 1 ≤ (B : ℚ) then
            some (fc2kSliverCap sliver + tiles * wc.cap)
          else
            none

/-- Per-`J` quadratic central-mean enclosure check for `J ∈ [0, J_max]`. -/
def fc2kCheckQuadJ (P corrLo maxHi : ℕ) (sp : FC2KSubbandSpec) (J : ℕ) : Bool :=
  let max_hi_f : ℚ := (maxHi : ℚ) / (sp.X_lo : ℚ)
  let corr_lo_f : ℚ := (corrLo : ℚ) / (sp.X_hi : ℚ)
  let D_n : ℚ := ((sp.n_hi - sp.n_lo : ℕ) : ℚ)
  let a1 : ℚ := 959 / 2000 - sp.c_lo
  let B1 : ℚ := 12 * (P : ℚ) * (max_hi_f - sp.c_lo) +
    12 * (J : ℚ) * (203 / 400 - sp.c_lo) +
    3 * (sp.W_ord : ℚ) * (4 * (491 / 1000) + 2 * sp.δ - 4 * sp.c_lo)
  let B0 : ℚ := 96 * (P : ℚ) * (max_hi_f - sp.c_lo) +
    96 * (J : ℚ) * (203 / 400 - sp.c_lo) +
    2 * (sp.W_diag : ℚ) * (4 * (491 / 1000) + 2 * sp.δ - 4 * sp.c_lo)
  let a2 : ℚ := sp.c_hi - 491 / 1000
  let C1 : ℚ := 12 * (P : ℚ) * (sp.c_hi - corr_lo_f) +
    12 * (J : ℚ) * (sp.c_hi - 197 / 400) +
    3 * (sp.W_ord : ℚ) * (4 * sp.c_hi - (4 * (959 / 2000) - 2 * sp.δ))
  let C0 : ℚ := 96 * (P : ℚ) * (sp.c_hi - corr_lo_f) +
    96 * (J : ℚ) * (sp.c_hi - 197 / 400) +
    2 * (sp.W_diag : ℚ) * (4 * sp.c_hi - (4 * (959 / 2000) - 2 * sp.δ))
  decide (
    0 ≤ (a1 * (sp.n_lo : ℚ) ^ 2 - B1 * (sp.n_lo : ℚ) - B0) +
      min 0 ((2 * a1 * (sp.n_lo : ℚ) - B1) * D_n) ∧
    0 ≤ (a2 * (sp.n_lo : ℚ) ^ 2 - C1 * (sp.n_lo : ℚ) - C0) +
      min 0 ((2 * a2 * (sp.n_lo : ℚ) - C1) * D_n)
  )

/-- Per-stage bridge budget check for `j ∈ [0, J_max)`. -/
def fc2kCheckBridgeStage (P corrLo maxHi : ℕ) (windowCaps octWindowCaps : List PrefixWindowCap)
    (sp : FC2KSubbandSpec) (j : ℕ) : Bool :=
  let u_hi : ℚ := (sp.b_X : ℚ) * fc2kLn2Hi / 128
  match sp.brStages[j]? with
  | none => false
  | some st =>
      let sp_lo : ℚ := min (fc2kBridgeRatioLo P sp.X_hi j) (1 / 2)
      let sp_hi : ℚ := min (fc2kBridgeRatioHi P sp.X_lo j) (1 / 2)
      let H_max : ℚ := (3 / 100 : ℚ) * sp_hi * (sp.X_hi : ℚ)
      let lo_low : ℚ := max (1 / 4 : ℚ) (1 / 2 - sp_hi / 2) * (sp.X_lo : ℚ)
      let lo_high : ℚ := (1 / 2 + (47 / 100 : ℚ) * sp_lo) * (sp.X_lo : ℚ)
      match evalWindowWitness corrLo maxHi windowCaps octWindowCaps lo_low H_max st.wLow,
            evalWindowWitness corrLo maxHi windowCaps octWindowCaps lo_high H_max st.wHigh with
      | some cap_low, some cap_high =>
          let ov : ℕ := if j = 0 then 0 else 1
          let k_max : ℕ := 24 + 3 * sp.n_hi
          let need : ℕ := st.M + 2 * k_max + max cap_low cap_high + 2 * k_max * ov
          let num_lb : ℚ := (sp.S_lo : ℚ) *
            ((3 / 100 : ℚ) * sp_lo * (sp.S_lo : ℚ) - (1036 / 125 : ℚ) * (8661 / 10000 : ℚ))
          decide (
            H_max + 1 < ((st.M * st.M : ℕ) : ℚ) ∧
            0 ≤ num_lb ∧
            (need : ℚ) * u_hi ≤ num_lb
          )
      | _, _ => false

/-- Full computable verification predicate for `FC2KSubbandSpec`. -/
def checkFC2KSubbandSpec (P qCert corrLo maxHi totalSpanWords : ℕ)
    (windowCaps octWindowCaps : List PrefixWindowCap)
    (sp : FC2KSubbandSpec) : Bool :=
  let u_lo : ℚ := (sp.a_X : ℚ) * fc2kLn2Lo / 128
  let u_hi : ℚ := (sp.b_X : ℚ) * fc2kLn2Hi / 128
  let u_Xh_lo : ℚ := (sp.a_Xh : ℚ) * fc2kLn2Lo / 128
  let l_wide_top : ℚ := 1 / 500 + (sp.N_bins : ℚ) * sp.δ
  let mwf : ℚ := 959 / 1000 - (1 / 250 + 2 * (sp.N_bins : ℚ) * sp.δ)
  let A_wide : ℚ := (sp.N_bins : ℚ) * sp.c_W
  let K_hi : ℕ := 2 * (2 * sp.W_diag + sp.W_ord * (3 * sp.n_hi)) + sp.N_bins
  let R0_wide : ℚ := A_wide * (sp.X_lo : ℚ) - (K_hi : ℚ)
  let max_hi_f : ℚ := (maxHi : ℚ) / (sp.X_lo : ℚ)
  let corr_lo_f : ℚ := (corrLo : ℚ) / (sp.X_hi : ℚ)
  let dsh_frac : ℚ := (6 : ℚ) / ((sp.n_lo * sp.n_lo - 1 : ℕ) : ℚ) * sp.ε
  let D_t75_f : ℚ :=
    if sp.n_hi ≤ 9299 then 23 / 50
    else ((sp.n_hi : ℚ) / 400) * (491 / 1000)
  let hiB_f : ℚ :=
    max (max (2 * max_hi_f) (max (203 / 200) (2 * (491 / 1000) + sp.δ))) (2 * sp.c_hi)
  let loB_f : ℚ :=
    min (min (2 * corr_lo_f) (min (197 / 200) (2 * (959 / 2000) - sp.δ))) (2 * sp.c_lo)
  let K_h : ℕ := 12 * P + 12 * sp.J_max + sp.W_diag
  decide (
    2001 ≤ sp.n_lo ∧ sp.n_lo ≤ sp.n_hi ∧ sp.n_hi ≤ 19483 ∧ 1 ≤ P ∧
    (sp.n_hi ≤ 9299 ∨ 9300 ≤ sp.n_lo) ∧
    6 * (sp.n_hi + 8) ≤ qCert ∧
    0 < sp.δ ∧ 0 < sp.ε ∧ 0 < sp.c_lo ∧ sp.c_lo < 959 / 2000 ∧ 491 / 1000 < sp.c_hi ∧
    -- X_lo & X_hi via direct monotone Li
    65170000 ≤ sp.X_lo ∧ sp.X_lo ≤ sp.X_hi ∧ sp.X_hi ≤ 4 * 10 ^ 13 ∧
    0 < sp.a_X ∧ 2 ^ sp.a_X < sp.X_lo ^ 128 ∧ sp.X_lo ≤ sp.S_lo_up * sp.S_lo_up ∧
    (sp.X_lo : ℚ) * bgLiUpperNormQ u_lo + (37 / 5 : ℚ) * (sp.S_lo_up : ℚ) / u_lo <
      ((sp.n_lo * sp.n_lo : ℕ) : ℚ) ∧
    0 < sp.b_X ∧ sp.X_hi ^ 128 < 2 ^ sp.b_X ∧
    0 < sp.a_Xh ∧ 2 ^ sp.a_Xh < sp.X_hi ^ 128 ∧ sp.X_hi ≤ sp.S_hi_up * sp.S_hi_up ∧
    ((sp.n_hi * sp.n_hi : ℕ) : ℚ) <
      (sp.X_hi : ℚ) * bgLiLowerNormQ u_hi - (37 / 5 : ℚ) * (sp.S_hi_up : ℚ) / u_Xh_lo ∧
    sp.S_lo * sp.S_lo ≤ sp.X_lo ∧ maxHi ≤ sp.X_lo ∧
    -- Bridge coverage & stages
    sp.brStages.length = sp.J_max ∧
    1 ≤ fc2kBridgeRatioLo P sp.X_hi sp.J_max ∧
    -- Wide checks
    0 < sp.c_W ∧ (1036 / 125 : ℚ) ≤ sp.δ * (sp.S_lo : ℚ) ∧
    sp.c_W * u_hi ≤ sp.δ - (1036 / 125 : ℚ) / (sp.S_lo : ℚ) ∧
    0 ≤ mwf ∧
    0 < R0_wide ∧ ((sp.N_bins * sp.X_lo : ℕ) : ℚ) ≤ R0_wide ^ 2 ∧
    (sp.N_bins : ℚ) ≤ 2 * A_wide * R0_wide ∧
    l_wide_top * (sp.X_hi : ℚ) < (corrLo : ℚ) ∧
    (maxHi : ℚ) ≤ (959 / 1000 - l_wide_top) * (sp.X_lo : ℚ) ∧
    l_wide_top < 1 / 4 ∧ 3 / 4 ≤ 959 / 1000 - l_wide_top ∧
    -- Packing & reservation checks
    2 * (24 * P + 24 * sp.J_max + 2 * sp.W_diag) + 1 ≤ sp.n_lo ∧
    4 * (12 * (P + sp.J_max + sp.W_ord) + 4) + 8 < sp.n_lo ∧
    4 * (12 * P * (sp.n_lo + 8) + 12 * sp.J_max * (sp.n_lo + 8) + 8 * sp.W_diag + 12 * sp.W_ord * sp.n_lo) ≤
      sp.n_lo * sp.n_lo ∧
    48 * (P + sp.J_max + sp.W_ord) ≤ 2 * sp.n_lo ∧
    -- Central separation & pool containment
    l_wide_top ≤ sp.c_lo - sp.ε - dsh_frac ∧
    sp.c_hi + sp.ε + dsh_frac ≤ 959 / 1000 - l_wide_top ∧
    1 ≤ (sp.c_lo - sp.ε - dsh_frac) * (sp.X_lo : ℚ) ∧
    sp.c_hi + sp.ε + dsh_frac ≤ 1 ∧
    -- Routing checks
    (2000 : ℚ) ≤ sp.c_N * (sp.X_lo : ℚ) ∧
    2 * sp.c_N ≤ 1 + (sp.W_ord : ℚ) * mwf ∧
    0 < sp.c_B ∧
    D_t75_f + (hiB_f - loB_f) + ((2 * totalSpanWords * 49152 : ℕ) : ℚ) / (sp.X_lo : ℚ) +
      (9 / 50 : ℚ) * (sp.J_max : ℚ) + 12 * (sp.W_ord : ℚ) * sp.δ +
      (1 + 10 * sp.ε) + (9 / 2 : ℚ) / (sp.X_lo : ℚ) ≤ 2 * sp.c_B ∧
    400000 * sp.c_B ≤ 199 * 999 * sp.c_N ∧
    400000 * (sp.c_B * (sp.X_lo : ℚ) + 1) + 199 * 999 ≤ 199 * 999 * sp.c_N * (sp.X_lo : ℚ) ∧
    -- Diagonal checks
    K_h ≤ sp.n_lo ∧
    (5 * 10 ^ 10 : ℚ) ≤ (((sp.n_lo - K_h : ℕ) : ℚ) * sp.c_lo - 2 * sp.ε) * (sp.X_lo : ℚ) ∧
    2 ≤ ((sp.n_lo - K_h : ℕ) : ℚ) * sp.c_lo - 2 * sp.ε ∧
    2 + (9 / 25 : ℚ) * (sp.J_max : ℚ) + (sp.W_diag : ℚ) * sp.δ + (401 / 100 : ℚ) * sp.ε +
      ((totalSpanWords * 49152 + 2 : ℕ) : ℚ) / (sp.X_lo : ℚ) ≤
      12 + (sp.W_diag : ℚ) * mwf
  ) &&
  (List.range (sp.J_max + 1)).all (fc2kCheckQuadJ P corrLo maxHi sp) &&
  (List.range sp.J_max).all (fc2kCheckBridgeStage P corrLo maxHi windowCaps octWindowCaps sp) &&
  (match evalWindowWitness corrLo maxHi windowCaps octWindowCaps
           ((sp.c_lo - sp.ε) * (sp.X_lo : ℚ)) ((sp.ε / 2) * (sp.X_hi : ℚ)) sp.wHalf,
         evalWindowWitness corrLo maxHi windowCaps octWindowCaps
           ((sp.c_lo - sp.ε - dsh_frac) * (sp.X_lo : ℚ))
           ((2 * sp.ε + 2 * dsh_frac) * (sp.X_hi : ℚ)) sp.wFull with
   | some P_half, some P_full =>
       let half_num : ℚ := (sp.S_lo : ℚ) * ((sp.ε / 2) * (sp.S_lo : ℚ) - 1036 / 125)
       let full_num : ℚ := (sp.S_lo : ℚ) * (2 * sp.ε * (sp.S_lo : ℚ) - 1036 / 125)
       decide (
         0 ≤ half_num ∧ 0 ≤ full_num ∧
         ((2 * sp.n_hi - 1 + 4 * sp.J_max * (24 + 3 * sp.n_hi) + P_half : ℕ) : ℚ) * u_hi ≤ half_num ∧
         ((3 * sp.n_hi + 1 + 4 * sp.J_max * (24 + 3 * sp.n_hi) + P_full + (2 * sp.n_hi - 1) : ℕ) : ℚ) * u_hi ≤ full_num
       )
   | _, _ => false)

noncomputable section

private theorem log_two_bounds_fc2k :
    (fc2kLn2Lo : ℝ) < Real.log 2 ∧ Real.log 2 < (fc2kLn2Hi : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  unfold fc2kLn2Lo fc2kLn2Hi
  push_cast
  exact ⟨by linarith, by linarith⟩

private theorem log_lower_of_pow_128 {a X : ℕ} (hX : 1 ≤ X) (hp : 2 ^ a < X ^ 128) :
    (((a : ℚ) * fc2kLn2Lo / 128 : ℚ) : ℝ) < Real.log (X : ℝ) := by
  have hXp : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpR : (2 : ℝ) ^ a < (X : ℝ) ^ 128 := by exact_mod_cast hp
  have hlg := Real.log_lt_log (by positivity) hpR
  rw [Real.log_pow, Real.log_pow] at hlg
  have hln2 := log_two_bounds_fc2k.1
  have ha_nn : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hmul : (a : ℝ) * (fc2kLn2Lo : ℝ) ≤ (a : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hln2.le ha_nn
  push_cast at hlg ⊢
  linarith

private theorem log_upper_of_pow_128 {b X : ℕ} (hX : 1 ≤ X) (hp : X ^ 128 < 2 ^ b) :
    Real.log (X : ℝ) < (((b : ℚ) * fc2kLn2Hi / 128 : ℚ) : ℝ) := by
  have hXp : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpR : (X : ℝ) ^ 128 < (2 : ℝ) ^ b := by exact_mod_cast hp
  have hlg := Real.log_lt_log (pow_pos hXp 128) hpR
  rw [Real.log_pow, Real.log_pow] at hlg
  have hln2 := log_two_bounds_fc2k.2
  have hb_nn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hmul : (b : ℝ) * Real.log 2 ≤ (b : ℝ) * (fc2kLn2Hi : ℝ) :=
    mul_le_mul_of_nonneg_left hln2.le hb_nn
  push_cast at hlg ⊢
  linarith

private theorem bgLiUpperNorm_anti {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hle : u₁ ≤ u₂) :
    bgLiUpperNorm u₂ ≤ bgLiUpperNorm u₁ := by
  unfold bgLiUpperNorm
  have h1 : 1 / u₂ ≤ 1 / u₁ := div_le_div_of_nonneg_left (by norm_num) hu₁ hle
  have h2 : 1 / u₂ ^ 2 ≤ 1 / u₁ ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hu₁ 2) (pow_le_pow_left₀ hu₁.le hle 2)
  have h3 : 4 / u₂ ^ 3 ≤ 4 / u₁ ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hu₁ 3) (pow_le_pow_left₀ hu₁.le hle 3)
  linarith

private theorem bgLiLowerNorm_anti {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hle : u₁ ≤ u₂) :
    bgLiLowerNorm u₂ ≤ bgLiLowerNorm u₁ := by
  unfold bgLiLowerNorm
  have h1 : 1 / u₂ ≤ 1 / u₁ := div_le_div_of_nonneg_left (by norm_num) hu₁ hle
  have h2 : 1 / u₂ ^ 2 ≤ 1 / u₁ ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hu₁ 2) (pow_le_pow_left₀ hu₁.le hle 2)
  have h3 : 2 / u₂ ^ 3 ≤ 2 / u₁ ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hu₁ 3) (pow_le_pow_left₀ hu₁.le hle 3)
  have h4 : 6 / u₂ ^ 4 ≤ 6 / u₁ ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hu₁ 4) (pow_le_pow_left₀ hu₁.le hle 4)
  linarith

private theorem bmor_sharp_poolMaximum_bounds (bmor : BMORFiniteTheta)
    {n n_lo n_hi a_X S_lo_up X_lo b_X a_Xh S_hi_up X_hi : ℕ}
    (hn_lo : n_lo ≤ n) (hn_hi : n ≤ n_hi)
    (hXlo_min : 65170000 ≤ X_lo) (hlo_hi : X_lo ≤ X_hi) (hXhi_max : X_hi ≤ 4 * 10 ^ 13)
    (ha_X_pos : 0 < a_X) (ha_X : 2 ^ a_X < X_lo ^ 128) (hS_lo_up : X_lo ≤ S_lo_up * S_lo_up)
    (hli_lo : (X_lo : ℚ) * bgLiUpperNormQ ((a_X : ℚ) * fc2kLn2Lo / 128) +
      (37 / 5 : ℚ) * (S_lo_up : ℚ) / ((a_X : ℚ) * fc2kLn2Lo / 128) < ((n_lo * n_lo : ℕ) : ℚ))
    (hb_X : X_hi ^ 128 < 2 ^ b_X)
    (ha_Xh_pos : 0 < a_Xh) (ha_Xh : 2 ^ a_Xh < X_hi ^ 128) (hS_hi_up : X_hi ≤ S_hi_up * S_hi_up)
    (hli_hi : ((n_hi * n_hi : ℕ) : ℚ) <
      (X_hi : ℚ) * bgLiLowerNormQ ((b_X : ℚ) * fc2kLn2Hi / 128) -
        (37 / 5 : ℚ) * (S_hi_up : ℚ) / ((a_Xh : ℚ) * fc2kLn2Lo / 128)) :
    (X_lo : ℝ) ≤ (poolMaximum n : ℝ) ∧
    (poolMaximum n : ℝ) ≤ (X_hi : ℝ) ∧
    Real.log (poolMaximum n : ℝ) ≤ (((b_X : ℚ) * fc2kLn2Hi / 128 : ℚ) : ℝ) := by
  have h1 : (X_lo : ℝ) ≤ (poolMaximum n : ℝ) := by
    by_contra hlt
    have hlt' : (poolMaximum n : ℝ) < (X_lo : ℝ) := lt_of_not_ge hlt
    have hX2 : (2 : ℝ) ≤ (poolMaximum n : ℝ) := by exact_mod_cast (poolMaximum_prime n).two_le
    have hX₀_ge : (65170000 : ℝ) ≤ (X_lo : ℝ) := by exact_mod_cast hXlo_min
    have hX₀_cap : (X_lo : ℝ) ≤ (4 * 10 ^ 13 : ℝ) := by exact_mod_cast (hlo_hi.trans hXhi_max)
    have hcnt := bmor_odd_count_uniform_bound_fc2k bmor hX₀_ge hX₀_cap (poolMaximum n : ℝ) hX2 hlt'.le
    rw [oddPrimeCountReal_natCast, oddPrimePrefix_poolMaximum_card] at hcnt
    have hmono := liFromTwo_mono hX2 hlt'.le
    have hbg := (bg_li_normalized_of_ge_65170000 hX₀_ge).2
    have hX₀_pos : (0 : ℝ) < (X_lo : ℝ) := by linarith
    have hbg' : liFromTwo (X_lo : ℝ) < (X_lo : ℝ) * bgLiUpperNorm (Real.log (X_lo : ℝ)) := by
      have := (div_lt_iff₀ hX₀_pos).mp hbg
      linarith
    let u_lo_q : ℚ := (a_X : ℚ) * fc2kLn2Lo / 128
    have hu_lo_pos : (0 : ℝ) < (u_lo_q : ℝ) := by
      dsimp [u_lo_q, fc2kLn2Lo]
      have : (0 : ℝ) < (a_X : ℝ) := Nat.cast_pos.mpr ha_X_pos
      positivity
    have hu_lo_lt : (u_lo_q : ℝ) < Real.log (X_lo : ℝ) :=
      log_lower_of_pow_128 (by omega) ha_X
    have hbg_anti := bgLiUpperNorm_anti hu_lo_pos hu_lo_lt.le
    have hsqrt_le : Real.sqrt (X_lo : ℝ) ≤ (S_lo_up : ℝ) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg S_lo_up), sq]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hS_lo_up)
    have herr_le : Real.sqrt (X_lo : ℝ) / Real.log (X_lo : ℝ) ≤ (S_lo_up : ℝ) / (u_lo_q : ℝ) := by
      calc Real.sqrt (X_lo : ℝ) / Real.log (X_lo : ℝ)
          ≤ (S_lo_up : ℝ) / Real.log (X_lo : ℝ) :=
            div_le_div_of_nonneg_right hsqrt_le (lt_trans hu_lo_pos hu_lo_lt).le
        _ ≤ (S_lo_up : ℝ) / (u_lo_q : ℝ) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) hu_lo_pos hu_lo_lt.le
    have hli_lo_R : (X_lo : ℝ) * bgLiUpperNorm (u_lo_q : ℝ) +
        (37 / 5 : ℝ) * ((S_lo_up : ℝ) / (u_lo_q : ℝ)) < ((n_lo * n_lo : ℕ) : ℝ) := by
      have hq := Rat.cast_lt (K := ℝ).mpr hli_lo
      unfold bgLiUpperNormQ at hq
      unfold bgLiUpperNorm
      dsimp [u_lo_q]
      push_cast at hq ⊢
      rw [← mul_div_assoc]
      exact hq
    have hn_sq : ((n_lo * n_lo : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul hn_lo hn_lo
    have hcnt1 := (abs_le.mp hcnt).2
    have hmul_bg := mul_le_mul_of_nonneg_left hbg_anti hX₀_pos.le
    linarith
  have h2 : (poolMaximum n : ℝ) ≤ (X_hi : ℝ) := by
    by_contra hgt
    have hgt' : (X_hi : ℝ) < (poolMaximum n : ℝ) := lt_of_not_ge hgt
    have hgt_nat : X_hi < poolMaximum n := by exact_mod_cast hgt'
    have hX₁_ge : (65170000 : ℝ) ≤ (X_hi : ℝ) := by exact_mod_cast (hXlo_min.trans hlo_hi)
    have hX₁_cap : (X_hi : ℝ) ≤ (4 * 10 ^ 13 : ℝ) := by exact_mod_cast hXhi_max
    have hcnt := bmor_odd_count_uniform_bound_fc2k bmor hX₁_ge hX₁_cap (X_hi : ℝ) (by linarith) le_rfl
    have hpref_le : (oddPrimePrefix X_hi).card ≤ n_hi * n_hi := by
      have hsub : oddPrimePrefix X_hi ⊆ oddPrimePrefix (poolMaximum n) :=
        Finset.filter_subset_filter _ (Finset.range_mono (by omega))
      exact (Finset.card_le_card hsub).trans
        ((oddPrimePrefix_poolMaximum_card n).le.trans (Nat.mul_le_mul hn_hi hn_hi))
    have hcnt_val : oddPrimeCountReal (X_hi : ℝ) ≤ ((n_hi * n_hi : ℕ) : ℝ) := by
      rw [oddPrimeCountReal_natCast]; exact_mod_cast hpref_le
    have hX₁_pos : (0 : ℝ) < (X_hi : ℝ) := by linarith
    have hbg := (bg_li_normalized_of_ge_65170000 hX₁_ge).1
    have hbg' : (X_hi : ℝ) * bgLiLowerNorm (Real.log (X_hi : ℝ)) < liFromTwo (X_hi : ℝ) := by
      have := (lt_div_iff₀ hX₁_pos).mp hbg
      linarith
    let u_hi_q : ℚ := (b_X : ℚ) * fc2kLn2Hi / 128
    let u_Xh_lo_q : ℚ := (a_Xh : ℚ) * fc2kLn2Lo / 128
    have hu_Xh_pos : (0 : ℝ) < (u_Xh_lo_q : ℝ) := by
      dsimp [u_Xh_lo_q, fc2kLn2Lo]
      have : (0 : ℝ) < (a_Xh : ℝ) := Nat.cast_pos.mpr ha_Xh_pos
      positivity
    have hu_Xh_lt : (u_Xh_lo_q : ℝ) < Real.log (X_hi : ℝ) :=
      log_lower_of_pow_128 (by omega) ha_Xh
    have hu_hi_gt : Real.log (X_hi : ℝ) < (u_hi_q : ℝ) :=
      log_upper_of_pow_128 (by omega) hb_X
    have hbg_anti := bgLiLowerNorm_anti (lt_trans hu_Xh_pos hu_Xh_lt) hu_hi_gt.le
    have hsqrt_le : Real.sqrt (X_hi : ℝ) ≤ (S_hi_up : ℝ) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg S_hi_up), sq]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hS_hi_up)
    have herr_le : Real.sqrt (X_hi : ℝ) / Real.log (X_hi : ℝ) ≤ (S_hi_up : ℝ) / (u_Xh_lo_q : ℝ) := by
      calc Real.sqrt (X_hi : ℝ) / Real.log (X_hi : ℝ)
          ≤ (S_hi_up : ℝ) / Real.log (X_hi : ℝ) :=
            div_le_div_of_nonneg_right hsqrt_le (lt_trans hu_Xh_pos hu_Xh_lt).le
        _ ≤ (S_hi_up : ℝ) / (u_Xh_lo_q : ℝ) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) hu_Xh_pos hu_Xh_lt.le
    have hli_hi_R : ((n_hi * n_hi : ℕ) : ℝ) <
        (X_hi : ℝ) * bgLiLowerNorm (u_hi_q : ℝ) -
          (37 / 5 : ℝ) * ((S_hi_up : ℝ) / (u_Xh_lo_q : ℝ)) := by
      have hq := Rat.cast_lt (K := ℝ).mpr hli_hi
      unfold bgLiLowerNormQ at hq
      unfold bgLiLowerNorm
      dsimp [u_hi_q, u_Xh_lo_q]
      push_cast at hq ⊢
      rw [← mul_div_assoc]
      exact hq
    have hcnt1 := (abs_le.mp hcnt).1
    have hmul_bg := mul_le_mul_of_nonneg_left hbg_anti hX₁_pos.le
    linarith
  have hXp : (0 : ℝ) < (poolMaximum n : ℝ) := by exact_mod_cast (poolMaximum_prime n).pos
  have hlog : Real.log (poolMaximum n : ℝ) ≤ (((b_X : ℚ) * fc2kLn2Hi / 128 : ℚ) : ℝ) :=
    (Real.log_le_log hXp h2).trans (log_upper_of_pow_128 (by omega) hb_X).le
  exact ⟨h1, h2, hlog⟩

private theorem primes_ge_five_Ioc_sliver_card {V : Finset ℕ}
    (hV : ∀ p ∈ V, Nat.Prime p ∧ 5 ≤ p) {u m sliver : ℕ} (hsub : m - u ≤ sliver) :
    (V ∩ Finset.Ioc u m).card ≤ fc2kSliverCap sliver := by
  unfold fc2kSliverCap
  split_ifs with hs0
  · subst hs0
    have hmu : m ≤ u := by omega
    rw [Finset.Ioc_eq_empty_of_le hmu, Finset.inter_empty, Finset.card_empty]
  · by_cases hmu : m ≤ u
    · rw [Finset.Ioc_eq_empty_of_le hmu, Finset.inter_empty, Finset.card_empty]
      exact Nat.zero_le _
    · have hmod6 : ∀ p ∈ V ∩ Finset.Ioc u m, p % 6 = 1 ∨ p % 6 = 5 := by
        intro p hp
        obtain ⟨hpP, hp5⟩ := hV p (Finset.mem_inter.mp hp).1
        have hnot2 : ¬ (2 ∣ p) := by
          intro hd
          rcases hpP.eq_one_or_self_of_dvd 2 hd with h | h <;> omega
        have hnot3 : ¬ (3 ∣ p) := by
          intro hd
          rcases hpP.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
        omega
      let f : ℕ → ℕ × Bool := fun p => (p / 6, decide (p % 6 = 5))
      have hinj : Set.InjOn f ↑(V ∩ Finset.Ioc u m) := by
        intro a ha b hb hfab
        have hma := hmod6 a ha
        have hmb := hmod6 b hb
        have hq : a / 6 = b / 6 := congrArg Prod.fst hfab
        have hr : decide (a % 6 = 5) = decide (b % 6 = 5) := congrArg Prod.snd hfab
        by_cases ha5 : a % 6 = 5
        · simp [ha5] at hr; omega
        · simp [ha5] at hr; omega
      have hmaps : (V ∩ Finset.Ioc u m).image f ⊆
          Finset.Icc (u / 6) (m / 6) ×ˢ (Finset.univ : Finset Bool) := by
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
        have hpi := Finset.mem_Ioc.mp (Finset.mem_inter.mp hp).2
        exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.div_le_div_right (le_of_lt hpi.1), Nat.div_le_div_right hpi.2⟩, Finset.mem_univ _⟩
      have hc1 : (V ∩ Finset.Ioc u m).card = ((V ∩ Finset.Ioc u m).image f).card :=
        (Finset.card_image_of_injOn hinj).symm
      have hc2 := Finset.card_le_card hmaps
      rw [Finset.card_product, Nat.card_Icc, Finset.card_univ, Fintype.card_bool] at hc2
      rw [hc1]
      omega

private theorem tiled_Ioc_word_cap {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    {wc : PrefixWindowCap} (hwc : wc ∈ prof.windowCaps) (hspan : 2 ≤ wc.spanWords)
    (tiles u v : ℕ) (hmin : corrLo + 49152 * wc.minWordIdx ≤ u)
    (hw : v - u ≤ tiles * ((wc.spanWords - 1) * 49152)) :
    ((Finset.univ.image prof.values) ∩ Finset.Ioc u v).card ≤ tiles * wc.cap := by
  set PSet := Finset.univ.image prof.values
  induction tiles generalizing u v with
  | zero =>
    have huv : v ≤ u := by omega
    simp [Finset.Ioc_eq_empty_of_le huv]
  | succ t ih =>
    set step := (wc.spanWords - 1) * 49152
    set mid := min v (u + step)
    have hsplit : Finset.Ioc u v ⊆ Finset.Ioc u mid ∪ Finset.Ioc mid v := by
      intro x hx
      have hx' := Finset.mem_Ioc.mp hx
      by_cases hxm : x ≤ mid
      · exact Finset.mem_union_left _ (Finset.mem_Ioc.mpr ⟨hx'.1, hxm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hxm, hx'.2⟩)
    have h1 : (PSet ∩ Finset.Ioc u mid).card ≤ wc.cap := by
      apply prof.window_cap wc hwc u mid hmin
      have hmid_le : mid ≤ u + (wc.spanWords - 1) * 49152 := min_le_right _ _
      have hmul : (wc.spanWords - 1) * 49152 + 49152 = 49152 * wc.spanWords := by
        calc (wc.spanWords - 1) * 49152 + 49152 = ((wc.spanWords - 1) + 1) * 49152 := by ring
          _ = 49152 * wc.spanWords := by rw [Nat.sub_add_cancel (by omega), Nat.mul_comm]
      omega
    have h2 : (PSet ∩ Finset.Ioc mid v).card ≤ t * wc.cap := by
      by_cases hvm : v ≤ u + step
      · dsimp [mid]
        rw [min_eq_left hvm, Finset.Ioc_self, Finset.inter_empty, Finset.card_empty]
        exact Nat.zero_le _
      · have hmu : mid = u + step := min_eq_right (le_of_not_ge hvm)
        apply ih mid v (by omega)
        rw [hmu]
        have : (t + 1) * step = step + t * step := by ring
        omega
    have hsub2 : PSet ∩ Finset.Ioc u v ⊆ (PSet ∩ Finset.Ioc u mid) ∪ (PSet ∩ Finset.Ioc mid v) := by
      intro x hx
      obtain ⟨hxP, hxI⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp (hsplit hxI) with hL | hR
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxP, hL⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxP, hR⟩)
    calc (PSet ∩ Finset.Ioc u v).card
        ≤ ((PSet ∩ Finset.Ioc u mid) ∪ (PSet ∩ Finset.Ioc mid v)).card := Finset.card_le_card hsub2
      _ ≤ (PSet ∩ Finset.Ioc u mid).card + (PSet ∩ Finset.Ioc mid v).card := Finset.card_union_le _ _
      _ ≤ wc.cap + t * wc.cap := Nat.add_le_add h1 h2
      _ = (t + 1) * wc.cap := by ring

private theorem tiled_Ioc_oct_cap {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    {wc : PrefixWindowCap} (hwc : wc ∈ prof.octWindowCaps) (hspan : 2 ≤ wc.spanWords)
    (tiles u v : ℕ) (hmin : corrLo + 393216 * wc.minWordIdx ≤ u)
    (hw : v - u ≤ tiles * ((wc.spanWords - 1) * 393216)) :
    ((Finset.univ.image prof.values) ∩ Finset.Ioc u v).card ≤ tiles * wc.cap := by
  set PSet := Finset.univ.image prof.values
  induction tiles generalizing u v with
  | zero =>
    have huv : v ≤ u := by omega
    simp [Finset.Ioc_eq_empty_of_le huv]
  | succ t ih =>
    set step := (wc.spanWords - 1) * 393216
    set mid := min v (u + step)
    have hsplit : Finset.Ioc u v ⊆ Finset.Ioc u mid ∪ Finset.Ioc mid v := by
      intro x hx
      have hx' := Finset.mem_Ioc.mp hx
      by_cases hxm : x ≤ mid
      · exact Finset.mem_union_left _ (Finset.mem_Ioc.mpr ⟨hx'.1, hxm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hxm, hx'.2⟩)
    have h1 : (PSet ∩ Finset.Ioc u mid).card ≤ wc.cap := by
      apply prof.oct_window_cap wc hwc u mid hmin
      have hmid_le : mid ≤ u + (wc.spanWords - 1) * 393216 := min_le_right _ _
      have hmul : (wc.spanWords - 1) * 393216 + 393216 = 393216 * wc.spanWords := by
        calc (wc.spanWords - 1) * 393216 + 393216 = ((wc.spanWords - 1) + 1) * 393216 := by ring
          _ = 393216 * wc.spanWords := by rw [Nat.sub_add_cancel (by omega), Nat.mul_comm]
      omega
    have h2 : (PSet ∩ Finset.Ioc mid v).card ≤ t * wc.cap := by
      by_cases hvm : v ≤ u + step
      · dsimp [mid]
        rw [min_eq_left hvm, Finset.Ioc_self, Finset.inter_empty, Finset.card_empty]
        exact Nat.zero_le _
      · have hmu : mid = u + step := min_eq_right (le_of_not_ge hvm)
        apply ih mid v (by omega)
        rw [hmu]
        have : (t + 1) * step = step + t * step := by ring
        omega
    have hsub2 : PSet ∩ Finset.Ioc u v ⊆ (PSet ∩ Finset.Ioc u mid) ∪ (PSet ∩ Finset.Ioc mid v) := by
      intro x hx
      obtain ⟨hxP, hxI⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp (hsplit hxI) with hL | hR
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxP, hL⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxP, hR⟩)
    calc (PSet ∩ Finset.Ioc u v).card
        ≤ ((PSet ∩ Finset.Ioc u mid) ∪ (PSet ∩ Finset.Ioc mid v)).card := Finset.card_le_card hsub2
      _ ≤ (PSet ∩ Finset.Ioc u mid).card + (PSet ∩ Finset.Ioc mid v).card := Finset.card_union_le _ _
      _ ≤ wc.cap + t * wc.cap := Nat.add_le_add h1 h2
      _ = (t + 1) * wc.cap := by ring

private theorem evalWindowWitness_sound {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    {V : Finset ℕ} (hV : V ⊆ Finset.univ.image prof.values)
    {lo_min width_max : ℚ} {lo hi : ℝ} {w : FC2KWindowWitness} {cap_out : ℕ}
    (hlo0 : 0 ≤ lo) (hlo_ge : (lo_min : ℝ) ≤ lo) (hbc : lo ≤ hi)
    (hw_le : hi - lo ≤ (width_max : ℝ))
    (heval : evalWindowWitness corrLo maxHi prof.windowCaps prof.octWindowCaps lo_min width_max w = some cap_out) :
    (V ∩ apInterval lo hi 2 1).card ≤ cap_out := by
  have hP5 : ∀ p ∈ Finset.univ.image prof.values, Nat.Prime p ∧ 5 ≤ p := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact prof.prime_and_ge_five x
  cases w with
  | aboveMaxHi =>
    dsimp only [evalWindowWitness] at heval
    split_ifs at heval with hab
    cases heval
    have habR : (maxHi : ℝ) ≤ lo := (show (maxHi : ℝ) ≤ (lo_min : ℝ) by exact_mod_cast hab).trans hlo_ge
    rw [generalPrefixProfile_above_maxHi_cap prof hV hlo0 hbc habR]
  | wordCap idx tiles sliver =>
    dsimp only [evalWindowWitness] at heval
    cases hget : prof.windowCaps[idx]? with
    | none => rw [hget] at heval; cases heval
    | some wc =>
      rw [hget] at heval
      dsimp only at heval
      split_ifs at heval with hcond
      cases heval
      have hwc_mem : wc ∈ prof.windowCaps := List.mem_of_getElem? hget
      set m_start := corrLo + 49152 * wc.minWordIdx
      set B := tiles * ((wc.spanWords - 1) * 49152)
      set u := ⌊lo⌋₊
      set v := ⌊hi⌋₊
      have hu_lt : lo < (u : ℝ) + 1 := Nat.lt_floor_add_one lo
      have hv_le : (v : ℝ) ≤ hi := Nat.floor_le (hlo0.trans hbc)
      have hm_sliver : m_start - u ≤ sliver := by
        have h1R : (m_start : ℝ) - (sliver : ℝ) ≤ (lo_min : ℝ) := by exact_mod_cast hcond.2.1
        by_cases hs0 : sliver = 0
        · subst hs0
          simp only [Nat.cast_zero, sub_zero] at h1R
          have hle_u : m_start ≤ u := Nat.le_floor (h1R.trans hlo_ge)
          omega
        · have hlt_R : (m_start : ℝ) < ((u + sliver + 1 : ℕ) : ℝ) := by push_cast; linarith
          have hlt_N : m_start < u + sliver + 1 := Nat.cast_lt.mp hlt_R
          omega
      have hvu_B : v - u ≤ B := by
        have hBR : (width_max : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast hcond.2.2
        have hlt_R : (v : ℝ) < ((u + B : ℕ) : ℝ) := by push_cast; linarith
        have hlt_N : v < u + B := Nat.cast_lt.mp hlt_R
        omega
      set PSet := Finset.univ.image prof.values
      have hsub_ioc : V ∩ apInterval lo hi 2 1 ⊆ PSet ∩ Finset.Ioc u v :=
        Finset.inter_subset_inter hV (apInterval_subset_Ioc_floor hlo0 hbc)
      have hsplit : PSet ∩ Finset.Ioc u v ⊆
          (PSet ∩ Finset.Ioc u (min v m_start)) ∪ (PSet ∩ Finset.Ioc (max u m_start) v) := by
        intro x hx
        obtain ⟨hxP, hxI⟩ := Finset.mem_inter.mp hx
        have hx' := Finset.mem_Ioc.mp hxI
        by_cases hxm : x ≤ m_start
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxP, Finset.mem_Ioc.mpr ⟨hx'.1, le_min hx'.2 hxm⟩⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxP, Finset.mem_Ioc.mpr ⟨max_lt hx'.1 (lt_of_not_ge hxm), hx'.2⟩⟩)
      have hc1 : (PSet ∩ Finset.Ioc u (min v m_start)).card ≤ fc2kSliverCap sliver :=
        primes_ge_five_Ioc_sliver_card hP5 (by have := min_le_right v m_start; omega)
      have hc2 : (PSet ∩ Finset.Ioc (max u m_start) v).card ≤ tiles * wc.cap :=
        tiled_Ioc_word_cap prof hwc_mem hcond.1 tiles (max u m_start) v (le_max_right _ _)
          (by have := le_max_left u m_start; omega)
      exact (Finset.card_le_card (hsub_ioc.trans hsplit)).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add hc1 hc2))
  | octCap idx tiles sliver =>
    dsimp only [evalWindowWitness] at heval
    cases hget : prof.octWindowCaps[idx]? with
    | none => rw [hget] at heval; cases heval
    | some wc =>
      rw [hget] at heval
      dsimp only at heval
      split_ifs at heval with hcond
      cases heval
      have hwc_mem : wc ∈ prof.octWindowCaps := List.mem_of_getElem? hget
      set m_start := corrLo + 393216 * wc.minWordIdx
      set B := tiles * ((wc.spanWords - 1) * 393216)
      set u := ⌊lo⌋₊
      set v := ⌊hi⌋₊
      have hu_lt : lo < (u : ℝ) + 1 := Nat.lt_floor_add_one lo
      have hv_le : (v : ℝ) ≤ hi := Nat.floor_le (hlo0.trans hbc)
      have hm_sliver : m_start - u ≤ sliver := by
        have h1R : (m_start : ℝ) - (sliver : ℝ) ≤ (lo_min : ℝ) := by exact_mod_cast hcond.2.1
        by_cases hs0 : sliver = 0
        · subst hs0
          simp only [Nat.cast_zero, sub_zero] at h1R
          have hle_u : m_start ≤ u := Nat.le_floor (h1R.trans hlo_ge)
          omega
        · have hlt_R : (m_start : ℝ) < ((u + sliver + 1 : ℕ) : ℝ) := by push_cast; linarith
          have hlt_N : m_start < u + sliver + 1 := Nat.cast_lt.mp hlt_R
          omega
      have hvu_B : v - u ≤ B := by
        have hBR : (width_max : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast hcond.2.2
        have hlt_R : (v : ℝ) < ((u + B : ℕ) : ℝ) := by push_cast; linarith
        have hlt_N : v < u + B := Nat.cast_lt.mp hlt_R
        omega
      set PSet := Finset.univ.image prof.values
      have hsub_ioc : V ∩ apInterval lo hi 2 1 ⊆ PSet ∩ Finset.Ioc u v :=
        Finset.inter_subset_inter hV (apInterval_subset_Ioc_floor hlo0 hbc)
      have hsplit : PSet ∩ Finset.Ioc u v ⊆
          (PSet ∩ Finset.Ioc u (min v m_start)) ∪ (PSet ∩ Finset.Ioc (max u m_start) v) := by
        intro x hx
        obtain ⟨hxP, hxI⟩ := Finset.mem_inter.mp hx
        have hx' := Finset.mem_Ioc.mp hxI
        by_cases hxm : x ≤ m_start
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxP, Finset.mem_Ioc.mpr ⟨hx'.1, le_min hx'.2 hxm⟩⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxP, Finset.mem_Ioc.mpr ⟨max_lt hx'.1 (lt_of_not_ge hxm), hx'.2⟩⟩)
      have hc1 : (PSet ∩ Finset.Ioc u (min v m_start)).card ≤ fc2kSliverCap sliver :=
        primes_ge_five_Ioc_sliver_card hP5 (by have := min_le_right v m_start; omega)
      have hc2 : (PSet ∩ Finset.Ioc (max u m_start) v).card ≤ tiles * wc.cap :=
        tiled_Ioc_oct_cap prof hwc_mem hcond.1 tiles (max u m_start) v (le_max_right _ _)
          (by have := le_max_left u m_start; omega)
      exact (Finset.card_le_card (hsub_ioc.trans hsplit)).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add hc1 hc2))

private def unstoppedBridgeIter (X R₀ : ℝ) : ℕ → ℝ
  | 0 => R₀
  | j + 1 =>
      let R := unstoppedBridgeIter X R₀ j
      R + (94 / 100 : ℝ) * min R (X / 2)

private theorem bridgeIteration_eq_unstopped_of_lt {X R₀ : ℝ}
    (hX : 0 < X) (hR₀ : 0 < R₀) {j : ℕ} (hj : bridgeIteration X R₀ j < X) :
    ∀ i ≤ j, bridgeIteration X R₀ i = unstoppedBridgeIter X R₀ i := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi_lt : bridgeIteration X R₀ i < X :=
      lt_of_le_of_lt (bridgeIteration_mono X R₀ hX hR₀ (by omega : i ≤ j)) hj
    change bridgeNext X (bridgeIteration X R₀ i) =
      unstoppedBridgeIter X R₀ i + (94 / 100 : ℝ) * min (unstoppedBridgeIter X R₀ i) (X / 2)
    rw [bridgeNext, if_pos hi_lt, ih (by omega)]
    unfold bridgeGapLower bridgeWidth bridgeSpan
    ring

private theorem fc2kBridgeRatio_enclosure {P X_lo X_hi : ℕ} {X : ℝ}
    (hX_lo_pos : 0 < X_lo) (hlo : (X_lo : ℝ) ≤ X) (hhi : X ≤ (X_hi : ℝ)) (j : ℕ) :
    (fc2kBridgeRatioLo P X_hi j : ℝ) * X ≤
      unstoppedBridgeIter X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j ∧
    unstoppedBridgeIter X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j ≤
      (fc2kBridgeRatioHi P X_lo j : ℝ) * X := by
  have hX_pos : 0 < X := lt_of_lt_of_le (Nat.cast_pos.mpr hX_lo_pos) hlo
  have hX_hi_pos : (0 : ℝ) < (X_hi : ℝ) := lt_of_lt_of_le hX_pos hhi
  have hX_lo_R : (0 : ℝ) < (X_lo : ℝ) := Nat.cast_pos.mpr hX_lo_pos
  induction j with
  | zero =>
    simp only [fc2kBridgeRatioLo, fc2kBridgeRatioHi, unstoppedBridgeIter, Rat.cast_div,
      Rat.cast_natCast]
    have hR0_nn : (0 : ℝ) ≤ ((2 ^ (P + 1) - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor
    · rw [div_mul_eq_mul_div, div_le_iff₀ hX_hi_pos]
      exact mul_le_mul_of_nonneg_left hhi hR0_nn
    · rw [div_mul_eq_mul_div, le_div_iff₀ hX_lo_R]
      exact mul_le_mul_of_nonneg_left hlo hR0_nn
  | succ j ih =>
    simp only [fc2kBridgeRatioLo, fc2kBridgeRatioHi, unstoppedBridgeIter]
    push_cast
    have hmin_lo : min (fc2kBridgeRatioLo P X_hi j : ℝ) (1 / 2) * X ≤
        min (unstoppedBridgeIter X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j) (X / 2) := by
      rw [min_mul_of_nonneg _ _ hX_pos.le]
      exact min_le_min ih.1 (by linarith)
    have hmin_hi : min (unstoppedBridgeIter X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j) (X / 2) ≤
        min (fc2kBridgeRatioHi P X_lo j : ℝ) (1 / 2) * X := by
      rw [min_mul_of_nonneg _ _ hX_pos.le]
      exact min_le_min ih.2 (by linarith)
    constructor
    · rw [add_mul, mul_assoc]; linarith [ih.1, hmin_lo]
    · rw [add_mul, mul_assoc]; linarith [ih.2, hmin_hi]

private theorem rat_le_to_real {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) :=
  Rat.cast_le.mpr h

private theorem rat_lt_to_real {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) :=
  Rat.cast_lt.mpr h

private theorem rat_nn_to_real {a : ℚ} (h : 0 ≤ a) : (0 : ℝ) ≤ (a : ℝ) :=
  Rat.cast_nonneg.mpr h

private theorem rat_pos_to_real {a : ℚ} (h : 0 < a) : (0 : ℝ) < (a : ℝ) :=
  Rat.cast_pos.mpr h

private theorem fc2k_res_max_of_slope {n n_lo P J_max W_diag W_ord : ℕ}
    (hn_lo : n_lo ≤ n)
    (hres_lo : 4 * (12 * P * (n_lo + 8) + 12 * J_max * (n_lo + 8) + 8 * W_diag + 12 * W_ord * n_lo) ≤ n_lo * n_lo)
    (hres_slope : 48 * (P + J_max + W_ord) ≤ 2 * n_lo) :
    4 * (12 * P * (n + 8) + 12 * J_max * (n + 8) + 8 * W_diag + 12 * W_ord * n) ≤ n * n := by
  set t_n := n - n_lo
  have hn_eq : n = n_lo + t_n := by omega
  rw [hn_eq]
  nlinarith

private theorem fc2k_res_J_le_sq {n n_lo P J J_max W_diag W_ord : ℕ}
    (hn_lo : n_lo ≤ n) (hJ : J ≤ J_max)
    (hres_lo : 4 * (12 * P * (n_lo + 8) + 12 * J_max * (n_lo + 8) + 8 * W_diag + 12 * W_ord * n_lo) ≤ n_lo * n_lo)
    (hres_slope : 48 * (P + J_max + W_ord) ≤ 2 * n_lo) :
    12 * P * (n + 8) + 12 * J * (n + 8) + 8 * W_diag + 12 * W_ord * n ≤ n * n := by
  have hmax := fc2k_res_max_of_slope hn_lo hres_lo hres_slope
  have hJ_mul : 12 * J * (n + 8) ≤ 12 * J_max * (n + 8) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hJ)
  omega

private theorem fc2k_mu_bounds_of_quad
    {n P corrLo maxHi J : ℕ} (sp : FC2KSubbandSpec)
    (hn : 2001 ≤ n) (hn_lo : sp.n_lo ≤ n) (hn_hi : n ≤ sp.n_hi)
    (hX_lo_pos : 0 < sp.X_lo)
    (hX_ge_lo : (sp.X_lo : ℝ) ≤ (poolMaximum n : ℝ))
    (hX_le_hi : (poolMaximum n : ℝ) ≤ (sp.X_hi : ℝ))
    (hm_lo : (959 / 2000 : ℝ) * (poolMaximum n : ℝ) < fc2kPoolMean n)
    (hm_hi : fc2kPoolMean n < (491 / 1000 : ℝ) * (poolMaximum n : ℝ))
    (hc_lo_lt : sp.c_lo < 959 / 2000)
    (hc_hi_gt : 491 / 1000 < sp.c_hi)
    (hresJ : 12 * P * (n + 8) + 12 * J * (n + 8) + 8 * sp.W_diag + 12 * sp.W_ord * n ≤ n * n)
    (hqJ : fc2kCheckQuadJ P corrLo maxHi sp J = true) :
    let X : ℝ := (poolMaximum n : ℝ)
    let m : ℝ := fc2kPoolMean n
    let μ_lo : ℝ := (sp.c_lo : ℝ) * X
    let μ_hi : ℝ := (sp.c_hi : ℝ) * X
    let N_rem : ℝ := ((n * n - (12 * P * (n + 8) + 12 * J * (n + 8) + 8 * sp.W_diag + 12 * sp.W_ord * n) : ℕ) : ℝ)
    let S_lo : ℝ := 12 * (P : ℝ) * ((n : ℝ) + 8) * (corrLo : ℝ) +
      6 * (J : ℝ) * ((n : ℝ) + 8) * ((197 / 200 : ℝ) * X) +
      (2 * (sp.W_diag : ℝ) + (sp.W_ord : ℝ) * (3 * (n : ℝ))) * (4 * m - 2 * (sp.δ : ℝ) * X)
    let S_hi : ℝ := 12 * (P : ℝ) * ((n : ℝ) + 8) * (maxHi : ℝ) +
      6 * (J : ℝ) * ((n : ℝ) + 8) * ((203 / 200 : ℝ) * X) +
      (2 * (sp.W_diag : ℝ) + (sp.W_ord : ℝ) * (3 * (n : ℝ))) * (4 * m + 2 * (sp.δ : ℝ) * X)
    μ_lo * N_rem ≤ (Lucas.poolTotal n : ℝ) - S_hi ∧
    (Lucas.poolTotal n : ℝ) - S_lo ≤ μ_hi * N_rem := by
  unfold fc2kCheckQuadJ at hqJ
  simp only [decide_eq_true_eq] at hqJ
  set X : ℝ := (poolMaximum n : ℝ)
  set m : ℝ := fc2kPoolMean n
  have hX_pos : 0 < X := lt_of_lt_of_le (Nat.cast_pos.mpr hX_lo_pos) hX_ge_lo
  have htot_eq : (Lucas.poolTotal n : ℝ) = ((n * n : ℕ) : ℝ) * m := by
    have hn_pos : 0 < n * n := by nlinarith
    have hnR : ((n * n : ℕ) : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn_pos)
    dsimp [m, fc2kPoolMean]; field_simp
  have hmaxHi_bound : (maxHi : ℝ) ≤ ((maxHi : ℝ) / (sp.X_lo : ℝ)) * X := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.mpr hX_lo_pos)]
    exact mul_le_mul_of_nonneg_left hX_ge_lo (Nat.cast_nonneg _)
  have hcorrLo_bound : ((corrLo : ℝ) / (sp.X_hi : ℝ)) * X ≤ (corrLo : ℝ) := by
    have hXhi_pos : (0 : ℝ) < (sp.X_hi : ℝ) := lt_of_lt_of_le hX_pos hX_le_hi
    rw [div_mul_eq_mul_div, div_le_iff₀ hXhi_pos]
    exact mul_le_mul_of_nonneg_left hX_le_hi (Nat.cast_nonneg _)
  set t_n : ℝ := ((n - sp.n_lo : ℕ) : ℝ)
  have ht_nn : 0 ≤ t_n := Nat.cast_nonneg _
  have ht_le : t_n ≤ ((sp.n_hi - sp.n_lo : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
  have hnR_eq : (n : ℝ) = (sp.n_lo : ℝ) + t_n := by
    dsimp [t_n]; exact_mod_cast (show n = sp.n_lo + (n - sp.n_lo) by omega)
  dsimp only
  rw [Nat.cast_sub hresJ, htot_eq]
  push_cast
  constructor
  · have hq1 := rat_nn_to_real hqJ.1
    push_cast at hq1
    set a1 : ℝ := 959 / 2000 - (sp.c_lo : ℝ)
    set B1 : ℝ := 12 * (P : ℝ) * ((maxHi : ℝ) / (sp.X_lo : ℝ) - (sp.c_lo : ℝ)) +
      12 * (J : ℝ) * (203 / 400 - (sp.c_lo : ℝ)) +
      3 * (sp.W_ord : ℝ) * (4 * (491 / 1000) + 2 * (sp.δ : ℝ) - 4 * (sp.c_lo : ℝ))
    set B0 : ℝ := 96 * (P : ℝ) * ((maxHi : ℝ) / (sp.X_lo : ℝ) - (sp.c_lo : ℝ)) +
      96 * (J : ℝ) * (203 / 400 - (sp.c_lo : ℝ)) +
      2 * (sp.W_diag : ℝ) * (4 * (491 / 1000) + 2 * (sp.δ : ℝ) - 4 * (sp.c_lo : ℝ))
    have ha1_pos : 0 < a1 := by
      have hlt := rat_lt_to_real hc_lo_lt
      push_cast at hlt
      dsimp [a1]; linarith
    have hlin_min : min 0 ((2 * a1 * (sp.n_lo : ℝ) - B1) * ((sp.n_hi - sp.n_lo : ℕ) : ℝ)) ≤
        (2 * a1 * (sp.n_lo : ℝ) - B1) * t_n := by
      by_cases hb_nn : 0 ≤ 2 * a1 * (sp.n_lo : ℝ) - B1
      · exact (min_le_left _ _).trans (mul_nonneg hb_nn ht_nn)
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left ht_le (le_of_lt (lt_of_not_ge hb_nn)))
    have hpoly_nn : 0 ≤ a1 * (n : ℝ) ^ 2 - B1 * (n : ℝ) - B0 := by
      have hid : a1 * (n : ℝ) ^ 2 - B1 * (n : ℝ) - B0 =
          (a1 * (sp.n_lo : ℝ) ^ 2 - B1 * (sp.n_lo : ℝ) - B0) +
          (2 * a1 * (sp.n_lo : ℝ) - B1) * t_n + a1 * t_n ^ 2 := by
        rw [hnR_eq]; ring
      rw [hid]; nlinarith [sq_nonneg t_n]
    have hmul_poly := mul_nonneg hpoly_nn hX_pos.le
    have hs1 : 12 * (P : ℝ) * ((n : ℝ) + 8) * (maxHi : ℝ) ≤
        12 * (P : ℝ) * ((n : ℝ) + 8) * (((maxHi : ℝ) / (sp.X_lo : ℝ)) * X) :=
      mul_le_mul_of_nonneg_left hmaxHi_bound (by positivity)
    have hs2 : (2 * (sp.W_diag : ℝ) + (sp.W_ord : ℝ) * (3 * (n : ℝ))) * (4 * m + 2 * (sp.δ : ℝ) * X) ≤
        (2 * (sp.W_diag : ℝ) + (sp.W_ord : ℝ) * (3 * (n : ℝ))) *
          ((4 * (491 / 1000) + 2 * (sp.δ : ℝ)) * X) :=
      mul_le_mul_of_nonneg_left (by linarith [hm_hi]) (by positivity)
    have hs3 : (959 / 2000 : ℝ) * X * ((n : ℝ) * (n : ℝ)) ≤ ((n : ℝ) * (n : ℝ)) * m := by
      nlinarith [hm_lo, show (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) by positivity]
    dsimp [a1, B1, B0] at hmul_poly
    linarith
  · have hq2 := rat_nn_to_real hqJ.2
    push_cast at hq2
    set a2 : ℝ := (sp.c_hi : ℝ) - 491 / 1000
    set C1 : ℝ := 12 * (P : ℝ) * ((sp.c_hi : ℝ) - (corrLo : ℝ) / (sp.X_hi : ℝ)) +
      12 * (J : ℝ) * ((sp.c_hi : ℝ) - 197 / 400) +
      3 * (sp.W_ord : ℝ) * (4 * (sp.c_hi : ℝ) - (4 * (959 / 2000) - 2 * (sp.δ : ℝ)))
    set C0 : ℝ := 96 * (P : ℝ) * ((sp.c_hi : ℝ) - (corrLo : ℝ) / (sp.X_hi : ℝ)) +
      96 * (J : ℝ) * ((sp.c_hi : ℝ) - 197 / 400) +
      2 * (sp.W_diag : ℝ) * (4 * (sp.c_hi : ℝ) - (4 * (959 / 2000) - 2 * (sp.δ : ℝ)))
    have ha2_pos : 0 < a2 := by
      have hgt := rat_lt_to_real hc_hi_gt
      push_cast at hgt
      dsimp [a2]; linarith
    have hlin_min : min 0 ((2 * a2 * (sp.n_lo : ℝ) - C1) * ((sp.n_hi - sp.n_lo : ℕ) : ℝ)) ≤
        (2 * a2 * (sp.n_lo : ℝ) - C1) * t_n := by
      by_cases hb_nn : 0 ≤ 2 * a2 * (sp.n_lo : ℝ) - C1
      · exact (min_le_left _ _).trans (mul_nonneg hb_nn ht_nn)
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left ht_le (le_of_lt (lt_of_not_ge hb_nn)))
    have hpoly_nn : 0 ≤ a2 * (n : ℝ) ^ 2 - C1 * (n : ℝ) - C0 := by
      have hid : a2 * (n : ℝ) ^ 2 - C1 * (n : ℝ) - C0 =
          (a2 * (sp.n_lo : ℝ) ^ 2 - C1 * (sp.n_lo : ℝ) - C0) +
          (2 * a2 * (sp.n_lo : ℝ) - C1) * t_n + a2 * t_n ^ 2 := by
        rw [hnR_eq]; ring
      rw [hid]; nlinarith [sq_nonneg t_n]
    have hmul_poly := mul_nonneg hpoly_nn hX_pos.le
    have hs1 : 12 * (P : ℝ) * ((n : ℝ) + 8) * (((corrLo : ℝ) / (sp.X_hi : ℝ)) * X) ≤
        12 * (P : ℝ) * ((n : ℝ) + 8) * (corrLo : ℝ) :=
      mul_le_mul_of_nonneg_left hcorrLo_bound (by positivity)
    have hs2 : (2 * (sp.W_diag : ℝ) + (sp.W_ord : ℝ) * (3 * (n : ℝ))) *
          ((4 * (959 / 2000) - 2 * (sp.δ : ℝ)) * X) ≤
        (2 * (sp.W_diag : ℝ) + (sp.W_ord : ℝ) * (3 * (n : ℝ))) * (4 * m - 2 * (sp.δ : ℝ) * X) :=
      mul_le_mul_of_nonneg_left (by linarith [hm_lo]) (by positivity)
    have hs3 : ((n : ℝ) * (n : ℝ)) * m ≤ (491 / 1000 : ℝ) * X * ((n : ℝ) * (n : ℝ)) := by
      nlinarith [hm_hi, show (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) by positivity]
    dsimp [a2, C1, C0] at hmul_poly
    linarith

private theorem two_pow_succ_sub_two_pos {P : ℕ} (hP : 1 ≤ P) :
    (0 : ℝ) < ((2 ^ (P + 1) - 2 : ℕ) : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hP
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have heq : 2 ^ (1 + k + 1) = 4 * 2 ^ k := by ring
  exact_mod_cast (show 0 < 2 ^ (1 + k + 1) - 2 by omega)

private theorem fc2k_dsh_le (sp : FC2KSubbandSpec) {n : ℕ}
    (hn2001 : 2001 ≤ sp.n_lo) (hn_lo : sp.n_lo ≤ n) (hε_q : 0 < sp.ε)
    {X : ℝ} (hX_pos : 0 < X) :
    6 * ((sp.ε : ℝ) * X) / ((n * n - 1 : ℕ) : ℝ) ≤
      (((6 : ℚ) / ((sp.n_lo * sp.n_lo - 1 : ℕ) : ℚ) * sp.ε : ℚ) : ℝ) * X := by
  push_cast
  have hlo_sq : 2001 * 2001 ≤ sp.n_lo * sp.n_lo := Nat.mul_le_mul hn2001 hn2001
  have hden_lo : (0 : ℝ) < ((sp.n_lo * sp.n_lo - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden_le : ((sp.n_lo * sp.n_lo - 1 : ℕ) : ℝ) ≤ ((n * n - 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by have := Nat.mul_le_mul hn_lo hn_lo; omega)
  have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6) hden_lo hden_le
  have hεX_nn : 0 ≤ (sp.ε : ℝ) * X := mul_nonneg (rat_nn_to_real hε_q.le) hX_pos.le
  calc 6 * ((sp.ε : ℝ) * X) / ((n * n - 1 : ℕ) : ℝ)
      = (6 / ((n * n - 1 : ℕ) : ℝ)) * ((sp.ε : ℝ) * X) := by ring
    _ ≤ (6 / ((sp.n_lo * sp.n_lo - 1 : ℕ) : ℝ)) * ((sp.ε : ℝ) * X) :=
        mul_le_mul_of_nonneg_right hdiv hεX_nn
    _ = 6 / ((sp.n_lo * sp.n_lo - 1 : ℕ) : ℝ) * (sp.ε : ℝ) * X := by ring

private theorem fc2k_br_budget_of_stage
    {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (sp : FC2KSubbandSpec)
    {n : ℕ} (hn_hi : n ≤ sp.n_hi) (hP : 1 ≤ P)
    (hX_lo_pos : 0 < sp.X_lo)
    (hX_ge_lo : (sp.X_lo : ℝ) ≤ (poolMaximum n : ℝ))
    (hX_le_hi : (poolMaximum n : ℝ) ≤ (sp.X_hi : ℝ))
    (hlog_le_uhi : Real.log (poolMaximum n : ℝ) ≤ (((sp.b_X : ℚ) * fc2kLn2Hi / 128 : ℚ) : ℝ))
    (hX_pos : 0 < (poolMaximum n : ℝ))
    (hlogX_pos : 0 < Real.log (poolMaximum n : ℝ))
    (hS_lo_le : (sp.S_lo : ℝ) ≤ Real.sqrt (poolMaximum n : ℝ))
    (hδ_Slo : (1036 / 125 : ℚ) ≤ sp.δ * (sp.S_lo : ℚ))
    (hbr_len : sp.brStages.length = sp.J_max)
    {V_pref : Finset ℕ} (hV_sub : V_pref ⊆ Finset.image prof.values Finset.univ)
    {j : ℕ} (hj_lt : j < sp.J_max)
    (hiter_lt : bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j < (poolMaximum n : ℝ))
    (hj_spec : fc2kCheckBridgeStage P corrLo maxHi prof.windowCaps prof.octWindowCaps sp j = true) :
    bridgeGeometricStageBudget n V_pref
      (bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ))
      (sp.brStages.getD j ⟨0, .aboveMaxHi, .aboveMaxHi⟩).M (24 + 3 * n) j := by
  let X : ℝ := (poolMaximum n : ℝ)
  let u_hi_q : ℚ := (sp.b_X : ℚ) * fc2kLn2Hi / 128
  have hu_hi_pos : (0 : ℝ) < (u_hi_q : ℝ) := lt_of_lt_of_le hlogX_pos hlog_le_uhi
  have hsqrt34_le : Real.sqrt (3 * X / 4) ≤ (8661 / 10000 : ℝ) * Real.sqrt X := by
    have hsq : 3 * X / 4 ≤ ((8661 / 10000 : ℝ) * Real.sqrt X) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hX_pos.le]; linarith
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))
  have hsqrt_quad : ∀ (c k : ℝ), 0 ≤ c → k ≤ c * (sp.S_lo : ℝ) →
      (sp.S_lo : ℝ) * (c * (sp.S_lo : ℝ) - k) ≤ c * X - k * Real.sqrt X := by
    intro c k hc hk
    have h1 : c * (sp.S_lo : ℝ) - k ≤ c * Real.sqrt X - k := by
      linarith [mul_le_mul_of_nonneg_left hS_lo_le hc]
    have h2 : (sp.S_lo : ℝ) * (c * (sp.S_lo : ℝ) - k) ≤ Real.sqrt X * (c * Real.sqrt X - k) :=
      mul_le_mul hS_lo_le h1 (by linarith) (Real.sqrt_nonneg X)
    have h3 : Real.sqrt X * (c * Real.sqrt X - k) = c * X - k * Real.sqrt X := by
      calc Real.sqrt X * (c * Real.sqrt X - k)
          = c * (Real.sqrt X * Real.sqrt X) - k * Real.sqrt X := by ring
        _ = c * X - k * Real.sqrt X := by rw [Real.mul_self_sqrt hX_pos.le]
    linarith
  unfold fc2kCheckBridgeStage at hj_spec
  have hj_len : j < sp.brStages.length := by omega
  have hget_j : sp.brStages[j]? = some (sp.brStages[j]'hj_len) := List.getElem?_eq_getElem hj_len
  rw [hget_j] at hj_spec
  set st := sp.brStages[j]'hj_len
  have hM_eq : (sp.brStages.getD j ⟨0, .aboveMaxHi, .aboveMaxHi⟩).M = st.M := by
    rw [List.getD_eq_getElem?_getD, hget_j]; rfl
  rw [hM_eq]
  let sp_lo_q : ℚ := min (fc2kBridgeRatioLo P sp.X_hi j) (1 / 2)
  let sp_hi_q : ℚ := min (fc2kBridgeRatioHi P sp.X_lo j) (1 / 2)
  let H_max_q : ℚ := (3 / 100 : ℚ) * sp_hi_q * (sp.X_hi : ℚ)
  let lo_low_q : ℚ := max (1 / 4 : ℚ) (1 / 2 - sp_hi_q / 2) * (sp.X_lo : ℚ)
  let lo_high_q : ℚ := (1 / 2 + (47 / 100 : ℚ) * sp_lo_q) * (sp.X_lo : ℚ)
  change (match
    evalWindowWitness corrLo maxHi prof.windowCaps prof.octWindowCaps lo_low_q H_max_q st.wLow,
    evalWindowWitness corrLo maxHi prof.windowCaps prof.octWindowCaps lo_high_q H_max_q st.wHigh with
    | some cap_low, some cap_high =>
      let ov : ℕ := if j = 0 then 0 else 1
      let k_max : ℕ := 24 + 3 * sp.n_hi
      let need : ℕ := st.M + 2 * k_max + max cap_low cap_high + 2 * k_max * ov
      let num_lb : ℚ := (sp.S_lo : ℚ) *
        ((3 / 100 : ℚ) * sp_lo_q * (sp.S_lo : ℚ) - (1036 / 125 : ℚ) * (8661 / 10000 : ℚ))
      decide (H_max_q + 1 < ((st.M * st.M : ℕ) : ℚ) ∧ 0 ≤ num_lb ∧ (need : ℚ) * u_hi_q ≤ num_lb)
    | _, _ => false) = true at hj_spec
  cases hwl : evalWindowWitness corrLo maxHi prof.windowCaps prof.octWindowCaps lo_low_q H_max_q st.wLow with
  | none => rw [hwl] at hj_spec; simp at hj_spec
  | some cap_low =>
    rw [hwl] at hj_spec
    cases hwhi : evalWindowWitness corrLo maxHi prof.windowCaps prof.octWindowCaps lo_high_q H_max_q st.wHigh with
    | none => rw [hwhi] at hj_spec; simp at hj_spec
    | some cap_high =>
      rw [hwhi] at hj_spec
      dsimp only at hj_spec
      simp only [decide_eq_true_eq] at hj_spec
      rcases hj_spec with ⟨hM_sq, hnum_nn, hneed_q⟩
      let R₀ : ℝ := ((2 ^ (P + 1) - 2 : ℕ) : ℝ)
      have hR0_pos : 0 < R₀ := two_pow_succ_sub_two_pos hP
      have heq_u := bridgeIteration_eq_unstopped_of_lt hX_pos hR0_pos hiter_lt j le_rfl
      obtain ⟨hr_lo, hr_hi⟩ := fc2kBridgeRatio_enclosure (P := P) hX_lo_pos hX_ge_lo hX_le_hi j
      set Rj := bridgeIteration X R₀ j
      have hRj_pos : 0 < Rj := bridgeIteration_pos X R₀ hX_pos hR0_pos j
      have hsp_lo : (sp_lo_q : ℝ) * X ≤ bridgeSpan X Rj := by
        dsimp [sp_lo_q]; push_cast
        rw [min_mul_of_nonneg _ _ hX_pos.le]
        exact min_le_min (by rw [heq_u]; exact hr_lo) (by linarith)
      have hsp_hi : bridgeSpan X Rj ≤ (sp_hi_q : ℝ) * X := by
        dsimp [sp_hi_q]; push_cast
        rw [min_mul_of_nonneg _ _ hX_pos.le]
        exact min_le_min (by rw [heq_u]; exact hr_hi) (by linarith)
      have hsp_lo_nn : 0 ≤ (sp_lo_q : ℝ) := by
        have : (0 : ℚ) ≤ fc2kBridgeRatioLo P sp.X_hi j := by
          clear * -
          induction j with
          | zero => unfold fc2kBridgeRatioLo; positivity
          | succ i ih => simp only [fc2kBridgeRatioLo]; positivity
        dsimp [sp_lo_q]; push_cast; exact le_min (rat_nn_to_real this) (by norm_num)
      have hH_le : bridgeWidth X Rj ≤ (H_max_q : ℝ) := by
        unfold bridgeWidth
        dsimp [H_max_q]; push_cast
        have hsp_hi_nn : 0 ≤ (sp_hi_q : ℝ) :=
          nonneg_of_mul_nonneg_left ((bridgeSpan_properties X Rj hX_pos hRj_pos).1.le.trans hsp_hi) hX_pos
        linarith [mul_le_mul_of_nonneg_left hX_le_hi hsp_hi_nn]
      have hg_j := bridge_window_geometry X Rj hX_pos hRj_pos
      have hlow_card : (V_pref ∩ bridgeLowStock X Rj).card ≤ cap_low := by
        apply evalWindowWitness_sound prof hV_sub (by linarith [hg_j.2.2.1]) _ hg_j.2.2.2.1.le
          (by rw [hg_j.2.2.2.2.2.2.2.1]; exact hH_le) hwl
        dsimp [lo_low_q]; push_cast
        rw [max_mul_of_nonneg _ _ (Nat.cast_nonneg _), max_le_iff]
        refine ⟨by linarith [hg_j.2.2.1], ?_⟩
        have h1 : (1 / 2 - (sp_hi_q : ℝ) / 2) * (sp.X_lo : ℝ) ≤ (1 / 2 - (sp_hi_q : ℝ) / 2) * X := by
          have hle12 : (sp_hi_q : ℝ) ≤ 1 / 2 := by dsimp [sp_hi_q]; push_cast; exact min_le_right _ _
          exact mul_le_mul_of_nonneg_left hX_ge_lo (by linarith)
        unfold bridgeLowStart
        linarith
      have hhigh_card : (V_pref ∩ bridgeHighStock X Rj).card ≤ cap_high := by
        apply evalWindowWitness_sound prof hV_sub
          (by linarith [hg_j.2.2.1, hg_j.2.2.2.1, hg_j.2.2.2.2.1]) _
          hg_j.2.2.2.2.2.1.le (by rw [hg_j.2.2.2.2.2.2.2.2]; exact hH_le) hwhi
        dsimp [lo_high_q]; push_cast
        have h1 : (1 / 2 + (47 / 100 : ℝ) * (sp_lo_q : ℝ)) * (sp.X_lo : ℝ) ≤
            (1 / 2 + (47 / 100 : ℝ) * (sp_lo_q : ℝ)) * X :=
          mul_le_mul_of_nonneg_left hX_ge_lo (by positivity)
        unfold bridgeHighStart bridgeHighEnd bridgeWidth
        linarith
      let ov : ℕ := if j = 0 then 0 else 1
      have hov_lo : (bridgeLowGeometricOverlap X (bridgeIteration X R₀) j).card ≤ ov := by
        by_cases hj0 : j = 0
        · subst hj0; simp [ov, bridgeLowGeometricOverlap, geometricallyOverlappingWindows]
        · simp [ov, hj0]; exact bridgeLowGeometricOverlap_card_le_one hX_pos hR0_pos hiter_lt
      have hov_hi : (bridgeHighGeometricOverlap X (bridgeIteration X R₀) j).card ≤ ov := by
        by_cases hj0 : j = 0
        · subst hj0; simp [ov, bridgeHighGeometricOverlap, geometricallyOverlappingWindows]
        · simp [ov, hj0]; exact bridgeHighGeometricOverlap_card_le_one hX_pos hR0_pos hiter_lt
      let num_lb_q : ℚ := (sp.S_lo : ℚ) *
        ((3 / 100 : ℚ) * sp_lo_q * (sp.S_lo : ℚ) - (1036 / 125 : ℚ) * (8661 / 10000 : ℚ))
      have hstock_ge : (num_lb_q : ℝ) / (u_hi_q : ℝ) ≤ bridgeStockBound X Rj := by
        unfold bridgeStockBound bridgeWidth
        have hnn : (0 : ℝ) ≤ (num_lb_q : ℝ) := rat_nn_to_real hnum_nn
        have hk_le : (1036 / 125 : ℝ) * (8661 / 10000 : ℝ) ≤ (3 / 100 : ℝ) * (sp_lo_q : ℝ) * (sp.S_lo : ℝ) := by
          have hSpos : (0 : ℝ) < (sp.S_lo : ℝ) := Nat.cast_pos.mpr (by
            have := hδ_Slo; by_contra h0; have h0' : sp.S_lo = 0 := by omega
            rw [h0'] at this; norm_num at this)
          have hnn' := hnn; dsimp [num_lb_q] at hnn'; push_cast at hnn'
          have := nonneg_of_mul_nonneg_right hnn' hSpos
          linarith
        have hq1 := hsqrt_quad ((3 / 100 : ℝ) * (sp_lo_q : ℝ)) ((1036 / 125 : ℝ) * (8661 / 10000 : ℝ))
          (by positivity) (by linarith)
        have hnum_le : (num_lb_q : ℝ) ≤
            (3 / 100 : ℝ) * bridgeSpan X Rj - 2 * (518 / 125 : ℝ) * Real.sqrt (3 * X / 4) := by
          dsimp [num_lb_q]; push_cast
          linarith [hq1, hsp_lo, hsqrt34_le]
        exact (div_le_div_of_nonneg_left hnn hlogX_pos hlog_le_uhi).trans
          (div_le_div_of_nonneg_right hnum_le hlogX_pos.le)
      let need_max := st.M + 2 * (24 + 3 * sp.n_hi) + max cap_low cap_high + 2 * (24 + 3 * sp.n_hi) * ov
      have hneed_R : (need_max : ℝ) ≤ (num_lb_q : ℝ) / (u_hi_q : ℝ) := by
        rw [le_div_iff₀ hu_hi_pos]
        have h : (need_max : ℚ) * u_hi_q ≤ num_lb_q := hneed_q
        exact_mod_cast h
      refine ⟨?_, ?_, ?_⟩
      · have hnat : st.M + 2 * (24 + 3 * n) + (V_pref ∩ bridgeLowStock X Rj).card +
            2 * (24 + 3 * n) * (bridgeLowGeometricOverlap X (bridgeIteration X R₀) j).card ≤ need_max := by
          have := le_max_left cap_low cap_high
          have : 2 * (24 + 3 * n) * (bridgeLowGeometricOverlap X (bridgeIteration X R₀) j).card ≤
              2 * (24 + 3 * sp.n_hi) * ov := Nat.mul_le_mul (by omega) hov_lo
          dsimp [need_max]; omega
        exact (show _ ≤ (need_max : ℝ) by exact_mod_cast hnat).trans (hneed_R.trans hstock_ge)
      · have hnat : st.M + 2 * (24 + 3 * n) + (V_pref ∩ bridgeHighStock X Rj).card +
            2 * (24 + 3 * n) * (bridgeHighGeometricOverlap X (bridgeIteration X R₀) j).card ≤ need_max := by
          have := le_max_right cap_low cap_high
          have : 2 * (24 + 3 * n) * (bridgeHighGeometricOverlap X (bridgeIteration X R₀) j).card ≤
              2 * (24 + 3 * sp.n_hi) * ov := Nat.mul_le_mul (by omega) hov_hi
          dsimp [need_max]; omega
        exact (show _ ≤ (need_max : ℝ) by exact_mod_cast hnat).trans (hneed_R.trans hstock_ge)
      · have hMR : (H_max_q : ℝ) + 1 < (st.M : ℝ) * (st.M : ℝ) := by
          have h := rat_lt_to_real hM_sq
          push_cast at h; exact h
        linarith

set_option maxHeartbeats 6400000 in
/-- Soundness of `checkFC2KSubbandSpec`: concludes `HasSquare n` for every odd `n ∈ [n_lo, n_hi]`. -/
theorem fc2k_hasSquare_of_spec
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (rs : RSPrimeCountImports)
    (upper : RSIndexUpper) (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (sp : FC2KSubbandSpec)
    (hspec : checkFC2KSubbandSpec P qCert corrLo maxHi prof.totalSpanWords
      prof.windowCaps prof.octWindowCaps sp = true)
    {n : ℕ} (hn_lo : sp.n_lo ≤ n) (hn_hi : n ≤ sp.n_hi) (hodd : Odd n) :
    HasSquare n := by
  unfold checkFC2KSubbandSpec at hspec
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hspec
  rcases hspec with ⟨⟨⟨hmain, hquad⟩, hbr_list⟩, hcent_win⟩
  rcases hmain with ⟨hn2001, hlo_le_hi, hnhi_max, hP, hn_split, hq_hi,
    hδ_q, hε_q, hc_lo_pos, hc_lo_lt, hc_hi_gt,
    hXlo_min, hXlo_le_Xhi, hXhi_max,
    ha_X_pos, ha_X_pow, hS_lo_up, hli_lo,
    hb_X_pos, hb_X_pow, ha_Xh_pos, ha_Xh_pow, hS_hi_up, hli_hi,
    hS_lo_sq, hmaxHi_Xlo,
    hbr_len, hJ_cov_q,
    hc_W_pos, hδ_Slo, hc_W_uhi, hmwf_nn, hR0w_pos, hR0w_sq, hR0w_lin,
    hpref_lo_q, hpref_hi_q, hbr_lo_q, hbr_hi_q,
    hs_max_lo, hload_max_lo, hres_lo, hres_slope,
    hcent_sep1, hcent_sep2, hcent_pool1, hcent_pool2,
    hc_N_min, hc_N_rad, hc_B_pos, hc_B_dem, hc_B_ratio, hc_B_cap,
    hKh_le, hdiag_5e10_q, hdiag_2X_q, hdiag_ov_q⟩
  have hn : 2001 ≤ n := le_trans hn2001 hn_lo
  have hnmax : n ≤ 19483 := le_trans hn_hi hnhi_max
  obtain ⟨hX_ge_lo, hX_le_hi, hlog_le_uhi⟩ :=
    bmor_sharp_poolMaximum_bounds bmor hn_lo hn_hi hXlo_min hXlo_le_Xhi hXhi_max
      ha_X_pos ha_X_pow hS_lo_up hli_lo hb_X_pow ha_Xh_pos ha_Xh_pow hS_hi_up hli_hi
  obtain ⟨hm_lo_raw, hm_hi_raw⟩ := fc2k_pool_mean_bounds bmor sharp upper hn hnmax
  let X : ℝ := (poolMaximum n : ℝ)
  let m : ℝ := fc2kPoolMean n
  have hm_lo : (959 / 2000 : ℝ) * X < m := hm_lo_raw
  have hm_hi : m < (491 / 1000 : ℝ) * X := hm_hi_raw
  have hX_lo_pos : 0 < sp.X_lo := by omega
  have hX_pos : 0 < X := lt_of_lt_of_le (Nat.cast_pos.mpr hX_lo_pos) hX_ge_lo
  have hlogX_pos : 0 < Real.log X :=
    Real.log_pos (by dsimp [X]; exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (poolMaximum_prime n).two_le))
  let u_hi_q : ℚ := (sp.b_X : ℚ) * fc2kLn2Hi / 128
  have hu_hi_pos : (0 : ℝ) < (u_hi_q : ℝ) := lt_of_lt_of_le hlogX_pos hlog_le_uhi
  have hS_lo_le : (sp.S_lo : ℝ) ≤ Real.sqrt X := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg sp.S_lo)]
    exact Real.sqrt_le_sqrt ((show (sp.S_lo : ℝ) ^ 2 ≤ (sp.X_lo : ℝ) by rw [sq]; exact_mod_cast hS_lo_sq).trans hX_ge_lo)
  -- Helper: `(S_lo : ℝ) * (c * (S_lo : ℝ) - k) ≤ c * X - k * √X` when `k ≤ c * S_lo`, `0 ≤ c`
  have hsqrt_quad : ∀ (c k : ℝ), 0 ≤ c → k ≤ c * (sp.S_lo : ℝ) →
      (sp.S_lo : ℝ) * (c * (sp.S_lo : ℝ) - k) ≤ c * X - k * Real.sqrt X := by
    intro c k hc hk
    have h1 : c * (sp.S_lo : ℝ) - k ≤ c * Real.sqrt X - k := by
      linarith [mul_le_mul_of_nonneg_left hS_lo_le hc]
    have h2 : (sp.S_lo : ℝ) * (c * (sp.S_lo : ℝ) - k) ≤ Real.sqrt X * (c * Real.sqrt X - k) :=
      mul_le_mul hS_lo_le h1 (by linarith) (Real.sqrt_nonneg X)
    have h3 : Real.sqrt X * (c * Real.sqrt X - k) = c * X - k * Real.sqrt X := by
      calc Real.sqrt X * (c * Real.sqrt X - k)
          = c * (Real.sqrt X * Real.sqrt X) - k * Real.sqrt X := by ring
        _ = c * X - k * Real.sqrt X := by rw [Real.mul_self_sqrt hX_pos.le]
    linarith
  -- Instantiate per-`n` Nat quantities `W_bin`, `N_cap`, `B_dem` and `M_br`
  let W_bin : ℕ := ⌊(sp.c_W : ℝ) * X⌋₊
  let N_cap : ℕ := ⌊(sp.c_N : ℝ) * X⌋₊
  let B_dem : ℕ := ⌈(sp.c_B : ℝ) * X⌉₊
  let μ_lo : ℝ := (sp.c_lo : ℝ) * X
  let μ_hi : ℝ := (sp.c_hi : ℝ) * X
  let M_br : ℕ → ℕ := fun j => (sp.brStages.getD j ⟨0, .aboveMaxHi, .aboveMaxHi⟩).M
  -- Extract P_half and P_full from `hcent_win`
  let dsh_frac : ℚ := (6 : ℚ) / ((sp.n_lo * sp.n_lo - 1 : ℕ) : ℚ) * sp.ε
  have hdsh_le : 6 * ((sp.ε : ℝ) * X) / ((n * n - 1 : ℕ) : ℝ) ≤ (dsh_frac : ℝ) * X :=
    fc2k_dsh_le sp hn2001 hn_lo hε_q hX_pos
  cases hwh : evalWindowWitness corrLo maxHi prof.windowCaps prof.octWindowCaps
      ((sp.c_lo - sp.ε) * (sp.X_lo : ℚ)) ((sp.ε / 2) * (sp.X_hi : ℚ)) sp.wHalf with
  | none => rw [hwh] at hcent_win; simp at hcent_win
  | some P_half =>
    rw [hwh] at hcent_win
    cases hwf : evalWindowWitness corrLo maxHi prof.windowCaps prof.octWindowCaps
        ((sp.c_lo - sp.ε - dsh_frac) * (sp.X_lo : ℚ))
        ((2 * sp.ε + 2 * dsh_frac) * (sp.X_hi : ℚ)) sp.wFull with
    | none => rw [hwf] at hcent_win; simp at hcent_win
    | some P_full =>
      rw [hwf] at hcent_win
      simp only [decide_eq_true_eq] at hcent_win
      rcases hcent_win with ⟨hhalf_nn, hfull_nn, hhalf_q, hfull_q⟩
      -- Apply `fc2k_subband_hasSquare`
      apply fc2k_subband_hasSquare bmor imp rs upper sharp upperSharp prof hn hnmax hodd hP
        (by omega)
        (hmaxHi_Xlo.trans (by exact_mod_cast hX_ge_lo))
        (rat_pos_to_real hδ_q)
        (rat_pos_to_real hε_q)
        (J_max := sp.J_max) (W_ord := sp.W_ord) (W_diag := sp.W_diag) (N_bins := sp.N_bins)
        (W_bin := W_bin) (P_half := P_half) (P_full := P_full)
        (N_cap := N_cap) (B_dem := B_dem) (μ_lo := μ_lo) (μ_hi := μ_hi) (M_br := M_br)
      · -- 1. `hJ_cover`
        by_contra hlt_cov
        have hlt_cov' : bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ) sp.J_max <
            (poolMaximum n : ℝ) := lt_of_not_ge hlt_cov
        have hR0_pos : (0 : ℝ) < ((2 ^ (P + 1) - 2 : ℕ) : ℝ) := two_pow_succ_sub_two_pos hP
        have heq_u := bridgeIteration_eq_unstopped_of_lt hX_pos hR0_pos hlt_cov' sp.J_max le_rfl
        have hlo_r := (fc2kBridgeRatio_enclosure (P := P) hX_lo_pos hX_ge_lo hX_le_hi sp.J_max).1
        have hcovR : (1 : ℝ) ≤ (fc2kBridgeRatioLo P sp.X_hi sp.J_max : ℝ) := by exact_mod_cast hJ_cov_q
        have h1X : X ≤ (fc2kBridgeRatioLo P sp.X_hi sp.J_max : ℝ) * X := by
          simpa using mul_le_mul_of_nonneg_right hcovR hX_pos.le
        dsimp [X] at heq_u hlo_r h1X
        linarith
      · -- 2. `hbr_budget`
        intro V_pref hV_sub _ j hj_lt hiter_lt
        exact fc2k_br_budget_of_stage prof sp hn_hi hP hX_lo_pos hX_ge_lo hX_le_hi hlog_le_uhi
          hX_pos hlogX_pos hS_lo_le hδ_Slo hbr_len hV_sub hj_lt hiter_lt (hbr_list j hj_lt)
      · -- 3. `hsep_mid`
        have hmwf_R := rat_nn_to_real hmwf_nn
        push_cast at hmwf_R
        have hm := mul_le_mul_of_nonneg_right hmwf_R hX_pos.le
        linarith [hm_lo]
      · -- 4. `hm_hi`
        linarith [hm_hi, hX_pos]
      · -- 5. `hW_bin`
        intro z
        have hX500 : (500 : ℝ) ≤ X := by linarith [show (65170000 : ℝ) ≤ X from
          (show (65170000 : ℝ) ≤ (sp.X_lo : ℝ) by exact_mod_cast hXlo_min).trans hX_ge_lo]
        have hsep_mid_here : ((1 / 250 : ℝ) + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ)) * X ≤ 2 * m := by
          have hmwf_R := rat_nn_to_real hmwf_nn
          push_cast at hmwf_R
          have hm := mul_le_mul_of_nonneg_right hmwf_R hX_pos.le
          linarith [hm_lo]
        obtain ⟨hb1, hbc_w, hcX_w, _, _, hlen_z⟩ :=
          fc2kWide_interval_props m X (sp.δ : ℝ) hX500 (rat_pos_to_real hδ_q) hsep_mid_here (by linarith)
        have hsl : Real.sqrt (fc2kWideLeft m X (sp.δ : ℝ) z) ≤ Real.sqrt X :=
          Real.sqrt_le_sqrt ((hbc_w z).trans (hcX_w z))
        have hsr : Real.sqrt (fc2kWideRight m X (sp.δ : ℝ) z) ≤ Real.sqrt X :=
          Real.sqrt_le_sqrt (hcX_w z)
        have hcW_nn : 0 ≤ (sp.c_W : ℝ) * X := mul_nonneg (rat_nn_to_real hc_W_pos.le) hX_pos.le
        have hWb_le : (W_bin : ℝ) ≤ (sp.c_W : ℝ) * X := Nat.floor_le hcW_nn
        have hSpos : (0 : ℝ) < (sp.S_lo : ℝ) := Nat.cast_pos.mpr (by
          have := hδ_Slo; by_contra h0; have h0' : sp.S_lo = 0 := by omega
          rw [h0'] at this; norm_num at this)
        have hX_div_S : Real.sqrt X ≤ X / (sp.S_lo : ℝ) := by
          rw [le_div_iff₀ hSpos]
          calc Real.sqrt X * (sp.S_lo : ℝ) ≤ Real.sqrt X * Real.sqrt X :=
                mul_le_mul_of_nonneg_left hS_lo_le (Real.sqrt_nonneg X)
            _ = X := Real.mul_self_sqrt hX_pos.le
        have hcW_R : (sp.c_W : ℝ) * (u_hi_q : ℝ) ≤ (sp.δ : ℝ) - (1036 / 125 : ℝ) / (sp.S_lo : ℝ) := by
          have h := rat_le_to_real hc_W_uhi
          dsimp [u_hi_q]
          push_cast at h ⊢
          exact h
        have h1 : (sp.c_W : ℝ) * X ≤ ((sp.δ : ℝ) * X - (1036 / 125 : ℝ) * Real.sqrt X) / (u_hi_q : ℝ) := by
          rw [le_div_iff₀ hu_hi_pos]
          have hm1 := mul_le_mul_of_nonneg_right hcW_R hX_pos.le
          have hm2 : ((1036 / 125 : ℝ) / (sp.S_lo : ℝ)) * X = (1036 / 125 : ℝ) * (X / (sp.S_lo : ℝ)) := by ring
          linarith
        have h2 : (0 : ℝ) ≤ (sp.δ : ℝ) * X - (1036 / 125 : ℝ) * Real.sqrt X := by
          have := mul_nonneg hcW_nn hu_hi_pos.le
          rw [le_div_iff₀ hu_hi_pos] at h1
          linarith
        have h3 : ((sp.δ : ℝ) * X - (1036 / 125 : ℝ) * Real.sqrt X) / (u_hi_q : ℝ) ≤
            ((sp.δ : ℝ) * X - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X :=
          div_le_div_of_nonneg_left h2 hlogX_pos hlog_le_uhi
        have h4 : ((sp.δ : ℝ) * X - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X ≤
            ((fc2kWideRight m X (sp.δ : ℝ) z - fc2kWideLeft m X (sp.δ : ℝ) z) -
              (518 / 125 : ℝ) * (Real.sqrt (fc2kWideLeft m X (sp.δ : ℝ) z) +
                Real.sqrt (fc2kWideRight m X (sp.δ : ℝ) z))) / Real.log X := by
          apply div_le_div_of_nonneg_right _ hlogX_pos.le
          rw [hlen_z z]
          linarith
        exact hWb_le.trans (h1.trans (h3.trans h4))
      · -- 6. `hwide_gate`
        let A_q : ℚ := (sp.N_bins : ℚ) * sp.c_W
        let K_hi : ℕ := 2 * (2 * sp.W_diag + sp.W_ord * (3 * sp.n_hi)) + sp.N_bins
        let R0_q : ℚ := A_q * (sp.X_lo : ℚ) - (K_hi : ℚ)
        have hWb_gt : (sp.c_W : ℝ) * X - 1 < (W_bin : ℝ) := Nat.sub_one_lt_floor _
        have hN_pos : 0 < sp.N_bins := by
          by_contra h0; have h0' : sp.N_bins = 0 := by omega
          have hr := hR0w_pos; rw [h0'] at hr
          have hnn : (0 : ℚ) ≤ ((2 * (2 * sp.W_diag + sp.W_ord * (3 * sp.n_hi)) + 0 : ℕ) : ℚ) := Nat.cast_nonneg _
          have hz : ((0 : ℕ) : ℚ) * sp.c_W * (sp.X_lo : ℚ) = 0 := by push_cast; ring
          linarith
        have hNWb : (A_q : ℝ) * X - (sp.N_bins : ℝ) < ((sp.N_bins * W_bin : ℕ) : ℝ) := by
          dsimp [A_q]; push_cast
          have := mul_lt_mul_of_pos_left hWb_gt (Nat.cast_pos.mpr hN_pos)
          linarith
        have hR0_pos_R : (0 : ℝ) < (R0_q : ℝ) := rat_pos_to_real hR0w_pos
        have hR0_sq_R : (sp.N_bins : ℝ) * (sp.X_lo : ℝ) ≤ (R0_q : ℝ) ^ 2 := by
          have h := rat_le_to_real hR0w_sq
          dsimp [R0_q, A_q, K_hi] at h ⊢
          push_cast at h ⊢; exact h
        have hR0_lin_R : (sp.N_bins : ℝ) ≤ 2 * (A_q : ℝ) * (R0_q : ℝ) := by
          have h := rat_le_to_real hR0w_lin
          dsimp [R0_q, A_q, K_hi] at h ⊢
          push_cast at h ⊢; exact h
        have hA_pos : (0 : ℝ) < (A_q : ℝ) := by
          dsimp [A_q]; push_cast; exact mul_pos (Nat.cast_pos.mpr hN_pos) (rat_pos_to_real hc_W_pos)
        set t := X - (sp.X_lo : ℝ)
        have ht_nn : 0 ≤ t := by dsimp [t]; linarith
        have hAX_eq : (A_q : ℝ) * X - (K_hi : ℝ) = (R0_q : ℝ) + (A_q : ℝ) * t := by
          dsimp [R0_q, t]; push_cast; ring
        have hAX_pos : 0 < (A_q : ℝ) * X - (K_hi : ℝ) := by
          rw [hAX_eq]
          have := mul_nonneg hA_pos.le ht_nn
          linarith
        have hk_le : 2 * (2 * sp.W_diag + sp.W_ord * (3 * n)) + sp.N_bins ≤ K_hi := by
          dsimp [K_hi]
          have := Nat.mul_le_mul_left sp.W_ord (show 3 * n ≤ 3 * sp.n_hi by omega)
          omega
        have hrem_gt : (A_q : ℝ) * X - (K_hi : ℝ) <
            ((sp.N_bins * W_bin - 2 * (2 * sp.W_diag + sp.W_ord * (3 * n)) : ℕ) : ℝ) := by
          have hkR : ((2 * (2 * sp.W_diag + sp.W_ord * (3 * n)) : ℕ) : ℝ) + (sp.N_bins : ℝ) ≤ (K_hi : ℝ) := by
            exact_mod_cast hk_le
          have hle_nat : 2 * (2 * sp.W_diag + sp.W_ord * (3 * n)) ≤ sp.N_bins * W_bin := by
            have : ((2 * (2 * sp.W_diag + sp.W_ord * (3 * n)) : ℕ) : ℝ) < ((sp.N_bins * W_bin : ℕ) : ℝ) := by linarith
            exact le_of_lt (Nat.cast_lt.mp this)
          rw [Nat.cast_sub hle_nat]
          linarith
        have hsq_ge : (sp.N_bins : ℝ) * X ≤ ((A_q : ℝ) * X - (K_hi : ℝ)) ^ 2 := by
          have h1 : ((A_q : ℝ) * X - (K_hi : ℝ)) ^ 2 =
              (R0_q : ℝ) ^ 2 + 2 * (A_q : ℝ) * (R0_q : ℝ) * t + ((A_q : ℝ) * t) ^ 2 := by
            rw [hAX_eq]; ring
          have h2 := mul_le_mul_of_nonneg_right hR0_lin_R ht_nn
          have h3 := sq_nonneg ((A_q : ℝ) * t)
          have h4 : (sp.N_bins : ℝ) * X = (sp.N_bins : ℝ) * (sp.X_lo : ℝ) + (sp.N_bins : ℝ) * t := by
            dsimp [t]; ring
          linarith
        exact lt_of_le_of_lt hsq_ge (pow_lt_pow_left₀ hrem_gt hAX_pos.le (by norm_num))
      · -- 7. `hpref_lo_wide`
        have h1 : ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) * (sp.X_hi : ℝ) < (corrLo : ℝ) := by
          have h := rat_lt_to_real hpref_lo_q; push_cast at h; exact h
        have h2 : ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) * X ≤
            ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) * (sp.X_hi : ℝ) :=
          mul_le_mul_of_nonneg_left hX_le_hi (by have : (0 : ℝ) < sp.δ := rat_pos_to_real hδ_q; positivity)
        linarith
      · -- 8. `hpref_hi_wide`
        have h1 : (maxHi : ℝ) ≤ ((959 / 1000 : ℝ) - ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ))) * (sp.X_lo : ℝ) := by
          have h := rat_le_to_real hpref_hi_q; push_cast at h; exact h
        have hcoef_nn : 0 ≤ (959 / 1000 : ℝ) - ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) := by
          have hmwf_R := rat_nn_to_real hmwf_nn; push_cast at hmwf_R
          have : 0 ≤ (sp.N_bins : ℝ) * (sp.δ : ℝ) :=
            mul_nonneg (Nat.cast_nonneg _) (rat_pos_to_real hδ_q).le
          linarith
        have h2 := mul_le_mul_of_nonneg_left hX_ge_lo hcoef_nn
        linarith [hm_lo]
      · -- 9. `hbr_lo_wide`
        have h1 : (1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ) < 1 / 4 := by
          have h := rat_lt_to_real hbr_lo_q; push_cast at h; exact h
        have hm := mul_lt_mul_of_pos_right h1 hX_pos
        linarith
      · -- 10. `hbr_hi_wide`
        have h1 : (3 / 4 : ℝ) ≤ (959 / 1000 : ℝ) - ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) := by
          have h := rat_le_to_real hbr_hi_q; push_cast at h; exact h
        have hm := mul_le_mul_of_nonneg_right h1 hX_pos.le
        linarith [hm_lo]
      · -- 11. `hs_max`
        omega
      · -- 12. `hload_max`
        omega
      · -- 13. `hres_max`
        exact fc2k_res_max_of_slope hn_lo hres_lo hres_slope
      · -- 14. `hμ_bounds`
        intro J hJ
        exact fc2k_mu_bounds_of_quad sp hn hn_lo hn_hi hX_lo_pos hX_ge_lo hX_le_hi
          hm_lo hm_hi hc_lo_lt hc_hi_gt
          (fc2k_res_J_le_sq hn_lo hJ hres_lo hres_slope)
          (hquad J (by omega))
      · -- 15. `hwide_sep_cent`
        dsimp only
        have hcs1 : ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) ≤
            (sp.c_lo : ℝ) - (sp.ε : ℝ) - (dsh_frac : ℝ) := by
          have h := rat_le_to_real hcent_sep1; dsimp [dsh_frac] at h ⊢; push_cast at h ⊢; exact h
        have hcs2 : (sp.c_hi : ℝ) + (sp.ε : ℝ) + (dsh_frac : ℝ) ≤
            (959 / 1000 : ℝ) - ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) := by
          have h := rat_le_to_real hcent_sep2; dsimp [dsh_frac] at h ⊢; push_cast at h ⊢; exact h
        have hm1 := mul_le_mul_of_nonneg_right hcs1 hX_pos.le
        have hm2 := mul_le_mul_of_nonneg_right hcs2 hX_pos.le
        dsimp [μ_lo, μ_hi]
        exact ⟨by linarith, by linarith [hm_lo]⟩
      · -- 16. `hcent_in_pool`
        dsimp only
        have hcp1 : (1 : ℝ) ≤ ((sp.c_lo : ℝ) - (sp.ε : ℝ) - (dsh_frac : ℝ)) * (sp.X_lo : ℝ) := by
          have h := rat_le_to_real hcent_pool1; dsimp [dsh_frac] at h ⊢; push_cast at h ⊢; exact h
        have hcoef_pos : 0 < (sp.c_lo : ℝ) - (sp.ε : ℝ) - (dsh_frac : ℝ) :=
          pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one hcp1) (Nat.cast_nonneg _)
        have hcp2 : (sp.c_hi : ℝ) + (sp.ε : ℝ) + (dsh_frac : ℝ) ≤ 1 := by
          have h := rat_le_to_real hcent_pool2; dsimp [dsh_frac] at h ⊢; push_cast at h ⊢; exact h
        have hm1 := mul_le_mul_of_nonneg_left hX_ge_lo hcoef_pos.le
        have hm2 := mul_le_mul_of_nonneg_right hcp2 hX_pos.le
        dsimp [μ_lo, μ_hi]
        exact ⟨by linarith, by linarith⟩
      · -- 17. `hP_half`
        intro V_pref hV_sub lo hi hlo_ge _ hbc hw_le
        have hcoef_nn : 0 ≤ (sp.c_lo : ℝ) - (sp.ε : ℝ) := by
          have hdsh_nn : 0 ≤ (dsh_frac : ℝ) := by
            dsimp [dsh_frac]; push_cast
            have : (0 : ℝ) ≤ sp.ε := rat_nn_to_real hε_q.le
            positivity
          have hcs1 : ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) ≤
              (sp.c_lo : ℝ) - (sp.ε : ℝ) - (dsh_frac : ℝ) := by
            have h := rat_le_to_real hcent_sep1; dsimp [dsh_frac] at h ⊢; push_cast at h ⊢; exact h
          have : 0 ≤ (sp.N_bins : ℝ) * (sp.δ : ℝ) :=
            mul_nonneg (Nat.cast_nonneg _) (rat_pos_to_real hδ_q).le
          linarith
        have hlo_min_R : (((sp.c_lo - sp.ε) * (sp.X_lo : ℚ) : ℚ) : ℝ) ≤ lo := by
          push_cast; dsimp [μ_lo] at hlo_ge
          have := mul_le_mul_of_nonneg_left hX_ge_lo hcoef_nn
          linarith
        have hlo0 : 0 ≤ lo := le_trans (by push_cast; exact mul_nonneg hcoef_nn (Nat.cast_nonneg _)) hlo_min_R
        have hw_max_R : hi - lo ≤ (((sp.ε / 2) * (sp.X_hi : ℚ) : ℚ) : ℝ) := by
          push_cast
          have : (0 : ℝ) ≤ sp.ε / 2 := by have : (0 : ℝ) < sp.ε := rat_pos_to_real hε_q; linarith
          linarith [mul_le_mul_of_nonneg_left hX_le_hi this]
        exact evalWindowWitness_sound prof hV_sub hlo0 hlo_min_R hbc hw_max_R hwh
      · -- 18. `hP_full`
        intro V_pref hV_sub lo hi
        dsimp only
        intro hlo_ge _ hbc hw_le
        have hdsh_nn : 0 ≤ (dsh_frac : ℝ) := by
          dsimp [dsh_frac]; push_cast
          have : (0 : ℝ) ≤ sp.ε := rat_nn_to_real hε_q.le
          positivity
        have hcoef_nn : 0 ≤ (sp.c_lo : ℝ) - (sp.ε : ℝ) - (dsh_frac : ℝ) := by
          have hcs1 : ((1 / 500 : ℝ) + (sp.N_bins : ℝ) * (sp.δ : ℝ)) ≤
              (sp.c_lo : ℝ) - (sp.ε : ℝ) - (dsh_frac : ℝ) := by
            have h := rat_le_to_real hcent_sep1; dsimp [dsh_frac] at h ⊢; push_cast at h ⊢; exact h
          have : 0 ≤ (sp.N_bins : ℝ) * (sp.δ : ℝ) :=
            mul_nonneg (Nat.cast_nonneg _) (rat_pos_to_real hδ_q).le
          linarith
        have hlo_min_R : (((sp.c_lo - sp.ε - dsh_frac) * (sp.X_lo : ℚ) : ℚ) : ℝ) ≤ lo := by
          push_cast; dsimp [μ_lo] at hlo_ge
          have := mul_le_mul_of_nonneg_left hX_ge_lo hcoef_nn
          linarith
        have hlo0 : 0 ≤ lo := le_trans (by push_cast; exact mul_nonneg hcoef_nn (Nat.cast_nonneg _)) hlo_min_R
        have hw_max_R : hi - lo ≤ (((2 * sp.ε + 2 * dsh_frac) * (sp.X_hi : ℚ) : ℚ) : ℝ) := by
          push_cast
          have hε_pos : (0 : ℝ) < sp.ε := rat_pos_to_real hε_q
          have hw1 : hi - lo ≤ (2 * (sp.ε : ℝ) + 2 * (dsh_frac : ℝ)) * X := by linarith
          exact hw1.trans (mul_le_mul_of_nonneg_left hX_le_hi (by linarith))
        exact evalWindowWitness_sound prof hV_sub hlo0 hlo_min_R hbc hw_max_R hwf
      · -- 19. `hhalf_gate`
        dsimp only
        let half_num_q : ℚ := (sp.S_lo : ℚ) * ((sp.ε / 2) * (sp.S_lo : ℚ) - 1036 / 125)
        have hnn : (0 : ℝ) ≤ (half_num_q : ℝ) := rat_nn_to_real hhalf_nn
        have hk_le : (1036 / 125 : ℝ) ≤ ((sp.ε : ℝ) / 2) * (sp.S_lo : ℝ) := by
          have hSpos : (0 : ℝ) < (sp.S_lo : ℝ) := Nat.cast_pos.mpr (by
            have := hδ_Slo; by_contra h0; have h0' : sp.S_lo = 0 := by omega
            rw [h0'] at this; norm_num at this)
          have hnn' := hnn; dsimp [half_num_q] at hnn'; push_cast at hnn'
          have := nonneg_of_mul_nonneg_right hnn' hSpos
          linarith
        have hq1 := hsqrt_quad ((sp.ε : ℝ) / 2) (1036 / 125)
          (by have : (0 : ℝ) < sp.ε := rat_pos_to_real hε_q; linarith) hk_le
        have hnum_le : (half_num_q : ℝ) ≤ ((sp.ε : ℝ) / 2) * X - (1036 / 125 : ℝ) * Real.sqrt X := by
          dsimp [half_num_q]; push_cast; linarith
        have hdiv_ge : (half_num_q : ℝ) / (u_hi_q : ℝ) ≤
            (((sp.ε : ℝ) / 2) * X - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X :=
          (div_le_div_of_nonneg_left hnn hlogX_pos hlog_le_uhi).trans
            (div_le_div_of_nonneg_right hnum_le hlogX_pos.le)
        have htot_R : ((2 * sp.n_hi - 1 + 4 * sp.J_max * (24 + 3 * sp.n_hi) + P_half : ℕ) : ℝ) ≤
            (half_num_q : ℝ) / (u_hi_q : ℝ) := by
          rw [le_div_iff₀ hu_hi_pos]
          have h := rat_le_to_real hhalf_q
          dsimp [u_hi_q, half_num_q] at h ⊢; push_cast at h ⊢; exact h
        have hnat_le : (2 * n - 1) + (4 * sp.J_max * (24 + 3 * n) + P_half) ≤
            2 * sp.n_hi - 1 + 4 * sp.J_max * (24 + 3 * sp.n_hi) + P_half := by
          have : 4 * sp.J_max * (24 + 3 * n) ≤ 4 * sp.J_max * (24 + 3 * sp.n_hi) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        have hnat_R : ((2 * n - 1 : ℕ) : ℝ) + ((4 * sp.J_max * (24 + 3 * n) + P_half : ℕ) : ℝ) ≤
            ((2 * sp.n_hi - 1 + 4 * sp.J_max * (24 + 3 * sp.n_hi) + P_half : ℕ) : ℝ) := by
          exact_mod_cast hnat_le
        linarith
      · -- 20. `hfull_gate`
        dsimp only
        let full_num_q : ℚ := (sp.S_lo : ℚ) * (2 * sp.ε * (sp.S_lo : ℚ) - 1036 / 125)
        have hnn : (0 : ℝ) ≤ (full_num_q : ℝ) := rat_nn_to_real hfull_nn
        have hk_le : (1036 / 125 : ℝ) ≤ (2 * (sp.ε : ℝ)) * (sp.S_lo : ℝ) := by
          have hSpos : (0 : ℝ) < (sp.S_lo : ℝ) := Nat.cast_pos.mpr (by
            have := hδ_Slo; by_contra h0; have h0' : sp.S_lo = 0 := by omega
            rw [h0'] at this; norm_num at this)
          have hnn' := hnn; dsimp [full_num_q] at hnn'; push_cast at hnn'
          have := nonneg_of_mul_nonneg_right hnn' hSpos
          linarith
        have hq1 := hsqrt_quad (2 * (sp.ε : ℝ)) (1036 / 125)
          (by have : (0 : ℝ) < sp.ε := rat_pos_to_real hε_q; linarith) hk_le
        have hnum_le : (full_num_q : ℝ) ≤ 2 * ((sp.ε : ℝ) * X) - (1036 / 125 : ℝ) * Real.sqrt X := by
          dsimp [full_num_q]; push_cast; linarith
        have hdiv_ge : (full_num_q : ℝ) / (u_hi_q : ℝ) ≤
            (2 * ((sp.ε : ℝ) * X) - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X :=
          (div_le_div_of_nonneg_left hnn hlogX_pos hlog_le_uhi).trans
            (div_le_div_of_nonneg_right hnum_le hlogX_pos.le)
        have htot_R : ((3 * sp.n_hi + 1 + 4 * sp.J_max * (24 + 3 * sp.n_hi) + P_full + (2 * sp.n_hi - 1) : ℕ) : ℝ) ≤
            (full_num_q : ℝ) / (u_hi_q : ℝ) := by
          rw [le_div_iff₀ hu_hi_pos]
          have h := rat_le_to_real hfull_q
          dsimp [u_hi_q, full_num_q] at h ⊢; push_cast at h ⊢; exact h
        have hnat_le : (3 * n + 1) + (4 * sp.J_max * (24 + 3 * n) + P_full + (2 * n - 1)) ≤
            3 * sp.n_hi + 1 + 4 * sp.J_max * (24 + 3 * sp.n_hi) + P_full + (2 * sp.n_hi - 1) := by
          have : 4 * sp.J_max * (24 + 3 * n) ≤ 4 * sp.J_max * (24 + 3 * sp.n_hi) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        have hnat_R : ((3 * n + 1 : ℕ) : ℝ) + ((4 * sp.J_max * (24 + 3 * n) + P_full + (2 * n - 1) : ℕ) : ℝ) ≤
            ((3 * sp.n_hi + 1 + 4 * sp.J_max * (24 + 3 * sp.n_hi) + P_full + (2 * sp.n_hi - 1) : ℕ) : ℝ) := by
          exact_mod_cast hnat_le
        linarith
      · -- 21. `hN_min`
        have hcN_R : (2000 : ℝ) ≤ (sp.c_N : ℝ) * (sp.X_lo : ℝ) := by
          have h := rat_le_to_real hc_N_min; push_cast at h; exact h
        have hcN_pos : 0 < (sp.c_N : ℝ) :=
          pos_of_mul_pos_left (lt_of_lt_of_le (by norm_num) hcN_R) (Nat.cast_nonneg _)
        exact Nat.le_floor (hcN_R.trans (mul_le_mul_of_nonneg_left hX_ge_lo hcN_pos.le))
      · -- 22. `hN_rad`
        have hcN_pos : 0 ≤ (sp.c_N : ℝ) := by
          have hcN_R : (2000 : ℝ) ≤ (sp.c_N : ℝ) * (sp.X_lo : ℝ) := by
            have h := rat_le_to_real hc_N_min; push_cast at h; exact h
          exact (pos_of_mul_pos_left (lt_of_lt_of_le (by norm_num) hcN_R) (Nat.cast_nonneg _)).le
        have hfl : (N_cap : ℝ) ≤ (sp.c_N : ℝ) * X := Nat.floor_le (mul_nonneg hcN_pos hX_pos.le)
        have hrad_R : 2 * (sp.c_N : ℝ) ≤ 1 + (sp.W_ord : ℝ) *
            ((959 / 1000 : ℝ) - (1 / 250 + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ))) := by
          have h := rat_le_to_real hc_N_rad; push_cast at h; exact h
        have hm1 := mul_le_mul_of_nonneg_right hrad_R hX_pos.le
        have hm2 : (sp.W_ord : ℝ) * ((959 / 1000 : ℝ) - (1 / 250 + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ))) * X ≤
            (sp.W_ord : ℝ) * (2 * m - ((1 / 250 : ℝ) + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ)) * X) :=
          by
            calc (sp.W_ord : ℝ) * ((959 / 1000 : ℝ) - (1 / 250 + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ))) * X
                = (sp.W_ord : ℝ) * (((959 / 1000 : ℝ) - (1 / 250 + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ))) * X) := by ring
              _ ≤ (sp.W_ord : ℝ) * (2 * m - ((1 / 250 : ℝ) + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ)) * X) :=
                mul_le_mul_of_nonneg_left (by linarith [hm_lo]) (Nat.cast_nonneg _)
        linarith
      · -- 23. `hB_cap`
        have hB_lt : (B_dem : ℝ) < (sp.c_B : ℝ) * X + 1 :=
          Nat.ceil_lt_add_one (mul_nonneg (rat_nn_to_real hc_B_pos.le) hX_pos.le)
        have hN_gt : (sp.c_N : ℝ) * X - 1 < (N_cap : ℝ) := Nat.sub_one_lt_floor _
        have hrat_R : 400000 * (sp.c_B : ℝ) ≤ 199 * 999 * (sp.c_N : ℝ) := by
          have h := rat_le_to_real hc_B_ratio; push_cast at h; exact h
        have hbase_R : 400000 * ((sp.c_B : ℝ) * (sp.X_lo : ℝ) + 1) + 199 * 999 ≤
            199 * 999 * (sp.c_N : ℝ) * (sp.X_lo : ℝ) := by
          have h := rat_le_to_real hc_B_cap; push_cast at h; exact h
        set t_x := X - (sp.X_lo : ℝ)
        have ht_nn : 0 ≤ t_x := by dsimp [t_x]; linarith
        have hlt_R : (400000 * B_dem : ℝ) < (199 * 999 * N_cap : ℝ) := by
          have hm_rat := mul_le_mul_of_nonneg_right hrat_R ht_nn
          have hX_split : X = (sp.X_lo : ℝ) + t_x := by dsimp [t_x]; ring
          rw [hX_split] at hB_lt hN_gt
          linarith
        exact_mod_cast hlt_R
      · -- 24. `hB_dem`
        dsimp only
        have hceil : (sp.c_B : ℝ) * X ≤ (B_dem : ℝ) := Nat.le_ceil _
        let D_t75_f_q : ℚ := if sp.n_hi ≤ 9299 then 23 / 50 else ((sp.n_hi : ℚ) / 400) * (491 / 1000)
        have hD_le : (if n ≤ 9299 then (23 / 50 : ℝ) * X else ((n : ℝ) * m) / 400) ≤ (D_t75_f_q : ℝ) * X := by
          rcases hn_split with hlow_band | hhigh_band
          · have hn9299 : n ≤ 9299 := le_trans hn_hi hlow_band
            dsimp [D_t75_f_q]; rw [if_pos hn9299, if_pos hlow_band]; norm_num
          · have hn_not : ¬ (n ≤ 9299) := by omega
            have hnhi_not : ¬ (sp.n_hi ≤ 9299) := by omega
            dsimp [D_t75_f_q]; rw [if_neg hn_not, if_neg hnhi_not]; push_cast
            have hn_le_R : (n : ℝ) ≤ (sp.n_hi : ℝ) := Nat.cast_le.mpr hn_hi
            have h1 : (n : ℝ) * m ≤ (n : ℝ) * ((491 / 1000 : ℝ) * X) :=
              mul_le_mul_of_nonneg_left hm_hi.le (Nat.cast_nonneg _)
            have h2 : (n : ℝ) * ((491 / 1000 : ℝ) * X) ≤ (sp.n_hi : ℝ) * ((491 / 1000 : ℝ) * X) :=
              mul_le_mul_of_nonneg_right hn_le_R (by positivity)
            linarith
        have hmaxHi_bound : 2 * (maxHi : ℝ) ≤ (2 * ((maxHi : ℝ) / (sp.X_lo : ℝ))) * X := by
          have : (maxHi : ℝ) ≤ ((maxHi : ℝ) / (sp.X_lo : ℝ)) * X := by
            rw [div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.mpr hX_lo_pos)]
            exact mul_le_mul_of_nonneg_left hX_ge_lo (Nat.cast_nonneg _)
          linarith
        have hcorrLo_bound : (2 * ((corrLo : ℝ) / (sp.X_hi : ℝ))) * X ≤ 2 * (corrLo : ℝ) := by
          have hXhi_pos : (0 : ℝ) < (sp.X_hi : ℝ) := lt_of_lt_of_le hX_pos hX_le_hi
          have : ((corrLo : ℝ) / (sp.X_hi : ℝ)) * X ≤ (corrLo : ℝ) := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hXhi_pos]
            exact mul_le_mul_of_nonneg_left hX_le_hi (Nat.cast_nonneg _)
          linarith
        let hiB_f_q : ℚ := max (max (2 * ((maxHi : ℚ) / (sp.X_lo : ℚ)))
          (max (203 / 200) (2 * (491 / 1000) + sp.δ))) (2 * sp.c_hi)
        let loB_f_q : ℚ := min (min (2 * ((corrLo : ℚ) / (sp.X_hi : ℚ)))
          (min (197 / 200) (2 * (959 / 2000) - sp.δ))) (2 * sp.c_lo)
        have hhiB_le : max (max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + (sp.δ : ℝ) * X)))
            (2 * μ_hi) ≤ (hiB_f_q : ℝ) * X := by
          dsimp [hiB_f_q, μ_hi]; push_cast
          rw [max_mul_of_nonneg _ _ hX_pos.le, max_mul_of_nonneg _ _ hX_pos.le, max_mul_of_nonneg _ _ hX_pos.le]
          exact max_le_max (max_le_max hmaxHi_bound (max_le_max le_rfl (by linarith [hm_hi]))) (by linarith)
        have hloB_ge : (loB_f_q : ℝ) * X ≤
            min (min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - (sp.δ : ℝ) * X))) (2 * μ_lo) := by
          dsimp [loB_f_q, μ_lo]; push_cast
          rw [min_mul_of_nonneg _ _ hX_pos.le, min_mul_of_nonneg _ _ hX_pos.le, min_mul_of_nonneg _ _ hX_pos.le]
          exact min_le_min (min_le_min hcorrLo_bound (min_le_min le_rfl (by linarith [hm_lo]))) (by linarith)
        have hspan_le : ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) ≤
            (((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) / (sp.X_lo : ℝ)) * X := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.mpr hX_lo_pos)]
          exact mul_le_mul_of_nonneg_left hX_ge_lo (Nat.cast_nonneg _)
        have h92_le : (9 / 2 : ℝ) ≤ ((9 / 2 : ℝ) / (sp.X_lo : ℝ)) * X := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.mpr hX_lo_pos)]
          exact mul_le_mul_of_nonneg_left hX_ge_lo (by norm_num)
        have hcB_R : (D_t75_f_q : ℝ) + ((hiB_f_q : ℝ) - (loB_f_q : ℝ)) +
            ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) / (sp.X_lo : ℝ) +
            (9 / 50 : ℝ) * (sp.J_max : ℝ) + 12 * (sp.W_ord : ℝ) * (sp.δ : ℝ) +
            (1 + 10 * (sp.ε : ℝ)) + (9 / 2 : ℝ) / (sp.X_lo : ℝ) ≤ 2 * (sp.c_B : ℝ) := by
          have hcast := rat_le_to_real hc_B_dem
          dsimp [D_t75_f_q, hiB_f_q, loB_f_q]
          push_cast at hcast ⊢
          exact hcast
        have hm_cB := mul_le_mul_of_nonneg_right hcB_R hX_pos.le
        linarith
      · -- 25. `hdiag_lo`
        let K_h := 12 * P + 12 * sp.J_max + sp.W_diag
        have h1 : (5 * 10 ^ 10 : ℝ) ≤ (((sp.n_lo - K_h : ℕ) : ℝ) * (sp.c_lo : ℝ) - 2 * (sp.ε : ℝ)) * (sp.X_lo : ℝ) := by
          have h := rat_le_to_real hdiag_5e10_q; dsimp [K_h] at h ⊢; push_cast at h ⊢; exact h
        have hcoef_pos : 0 ≤ ((sp.n_lo - K_h : ℕ) : ℝ) * (sp.c_lo : ℝ) - 2 * (sp.ε : ℝ) := by
          have h := rat_le_to_real hdiag_2X_q; dsimp [K_h] at h ⊢; push_cast at h; linarith
        have hcard_ge : ((sp.n_lo - K_h : ℕ) : ℝ) ≤ ((n - K_h : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
        have hc_lo_nn : 0 ≤ (sp.c_lo : ℝ) := rat_nn_to_real hc_lo_pos.le
        have hmul1 : (((sp.n_lo - K_h : ℕ) : ℝ) * (sp.c_lo : ℝ) - 2 * (sp.ε : ℝ)) * (sp.X_lo : ℝ) ≤
            (((sp.n_lo - K_h : ℕ) : ℝ) * (sp.c_lo : ℝ) - 2 * (sp.ε : ℝ)) * X :=
          mul_le_mul_of_nonneg_left hX_ge_lo hcoef_pos
        have hmul2 : ((sp.n_lo - K_h : ℕ) : ℝ) * (sp.c_lo : ℝ) * X ≤ ((n - K_h : ℕ) : ℝ) * (sp.c_lo : ℝ) * X :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard_ge hc_lo_nn) hX_pos.le
        dsimp [μ_lo, K_h] at hmul1 hmul2 ⊢
        linarith
      · -- 26. `hdiag_2X`
        let K_h := 12 * P + 12 * sp.J_max + sp.W_diag
        have h1 : (2 : ℝ) ≤ ((sp.n_lo - K_h : ℕ) : ℝ) * (sp.c_lo : ℝ) - 2 * (sp.ε : ℝ) := by
          have h := rat_le_to_real hdiag_2X_q; dsimp [K_h] at h ⊢; push_cast at h ⊢; exact h
        have hcard_ge : ((sp.n_lo - K_h : ℕ) : ℝ) ≤ ((n - K_h : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
        have hc_lo_nn : 0 ≤ (sp.c_lo : ℝ) := rat_nn_to_real hc_lo_pos.le
        have h2 : (2 : ℝ) ≤ ((n - K_h : ℕ) : ℝ) * (sp.c_lo : ℝ) - 2 * (sp.ε : ℝ) := by
          linarith [mul_le_mul_of_nonneg_right hcard_ge hc_lo_nn]
        have hm := mul_le_mul_of_nonneg_right h2 hX_pos.le
        dsimp [μ_lo, K_h] at hm ⊢
        linarith
      · -- 27. `hdiag_overlap`
        dsimp only
        have hov_R : 2 + (9 / 25 : ℝ) * (sp.J_max : ℝ) + (sp.W_diag : ℝ) * (sp.δ : ℝ) +
            (401 / 100 : ℝ) * (sp.ε : ℝ) +
            ((prof.totalSpanWords * 49152 + 2 : ℕ) : ℝ) / (sp.X_lo : ℝ) ≤
            12 + (sp.W_diag : ℝ) * ((959 / 1000 : ℝ) - (1 / 250 + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ))) := by
          have h := rat_le_to_real hdiag_ov_q; push_cast at h ⊢; linarith
        have hconst_le : ((prof.totalSpanWords * 49152 : ℕ) : ℝ) + 2 ≤
            (((prof.totalSpanWords * 49152 + 2 : ℕ) : ℝ) / (sp.X_lo : ℝ)) * X := by
          have heq : ((prof.totalSpanWords * 49152 : ℕ) : ℝ) + 2 = ((prof.totalSpanWords * 49152 + 2 : ℕ) : ℝ) := by
            push_cast; ring
          rw [heq, div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.mpr hX_lo_pos)]
          exact mul_le_mul_of_nonneg_left hX_ge_lo (Nat.cast_nonneg _)
        have hm_ov := mul_le_mul_of_nonneg_right hov_R hX_pos.le
        have hW_m : (sp.W_diag : ℝ) * ((959 / 1000 : ℝ) - (1 / 250 + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ))) * X ≤
            (sp.W_diag : ℝ) * (2 * m - ((1 / 250 : ℝ) + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ)) * X) := by
          calc (sp.W_diag : ℝ) * ((959 / 1000 : ℝ) - (1 / 250 + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ))) * X
              = (sp.W_diag : ℝ) * (((959 / 1000 : ℝ) - (1 / 250 + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ))) * X) := by ring
            _ ≤ (sp.W_diag : ℝ) * (2 * m - ((1 / 250 : ℝ) + 2 * (sp.N_bins : ℝ) * (sp.δ : ℝ)) * X) :=
              mul_le_mul_of_nonneg_left (by linarith [hm_lo]) (Nat.cast_nonneg _)
        linarith

end

end Sude
