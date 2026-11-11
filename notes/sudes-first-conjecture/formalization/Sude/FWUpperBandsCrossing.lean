import Sude.FWWheelFirstTraceStep
import Sude.FWFirstWindowRadius105
import Sude.FWFullStockNumericLower
import Sude.FWFullStockWitnessFromCharge
import Sude.BTChosenNarrowTrace
import Sude.FWBT16EntryGate
import Sude.FWThetaInputs
import Sude.FWWheelFirstBandEnvelopes

/-! Screened 238-stage crossing to `X / 23` for the upper FW and EW bands
    (`21249 ≤ n ≤ 35733`), split into Band A (`21249 ≤ n ≤ 27554`) and
    Band B (`27555 ≤ n ≤ 35733`), using the generic first-wheel, enhanced
    mixed-wheel, and Brun--Titchmarsh trace-extension engines. -/

set_option autoImplicit false

namespace Sude
noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

theorem log_lt_of_pow_lt_exp (y : ℝ) (p q : ℕ) (hy : 0 < y) (hq : 0 < q)
    (hpow : y ^ q < (2718281828 / 1000000000 : ℝ) ^ p) :
    Real.log y < (p : ℝ) / q := by
  have he1 : (2718281828 / 1000000000 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hepow : (2718281828 / 1000000000 : ℝ) ^ p ≤ Real.exp 1 ^ p :=
    pow_le_pow_left₀ (by norm_num) he1.le p
  have hexp : Real.exp 1 ^ p = Real.exp (p : ℝ) := by
    rw [← Real.exp_nat_mul, mul_one]
  have hlt : y ^ q < Real.exp (p : ℝ) := lt_of_lt_of_le hpow (hepow.trans_eq hexp)
  have hlog := Real.log_lt_log (pow_pos hy q) hlt
  rw [Real.log_pow, Real.log_exp] at hlog
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  exact (lt_div_iff₀ hqR).2 (by linarith)

theorem lt_log_of_exp_lt_pow (y : ℝ) (p q : ℕ) (_hy : 0 < y) (hq : 0 < q)
    (hpow : (2718281829 / 1000000000 : ℝ) ^ p < y ^ q) :
    (p : ℝ) / q < Real.log y := by
  have he1 : Real.exp 1 < (2718281829 / 1000000000 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hepow : Real.exp 1 ^ p ≤ (2718281829 / 1000000000 : ℝ) ^ p :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he1.le p
  have hexp : Real.exp (p : ℝ) = Real.exp 1 ^ p := by
    rw [← Real.exp_nat_mul, mul_one]
  have hlt : Real.exp (p : ℝ) < y ^ q := lt_of_le_of_lt (hexp.trans_le hepow) hpow
  have hlog := Real.log_lt_log (Real.exp_pos (p : ℝ)) hlt
  rw [Real.log_exp, Real.log_pow] at hlog
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  exact (div_lt_iff₀ hqR).2 (by linarith)

def btExpCeil : ℕ → ℕ
  | 15 => 3269019
  | 16 => 8886112
  | 17 => 24154954
  | _ => 0

theorem exp_le_btExpCeil {ell : ℕ} (hell : ell = 15 ∨ ell = 16 ∨ ell = 17) :
    Real.exp (ell : ℝ) ≤ btExpCeil ell := by
  have he1 : Real.exp 1 ≤ (2718281829 / 1000000000 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he1 ell
  have hid : Real.exp 1 ^ ell = Real.exp (ell : ℝ) := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hid] at hp
  rcases hell with rfl | rfl | rfl <;> {
    dsimp [btExpCeil]
    norm_num at hp ⊢
    linarith
  }

theorem even_gap_ge_two_mul_floor_half {D : ℝ} {gap : ℕ}
    (heven : 2 ∣ gap) (hD : D ≤ gap) :
    2 * ⌊D / 2⌋₊ ≤ gap := by
  by_cases hpos : 0 ≤ D / 2
  · obtain ⟨k, rfl⟩ := heven
    have hk : D / 2 ≤ k := by push_cast at hD; linarith
    have hf : ⌊D / 2⌋₊ ≤ k := Nat.floor_le_of_le hk
    omega
  · rw [Nat.floor_of_nonpos (le_of_not_ge hpos)]
    omega

theorem trace_last_even {Q : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial radius final last stages)
    (heven : 2 ∣ radius) : 2 ∣ last := by
  induction trace with
  | nil _ _ => exact heven
  | cons _ _ _ _ _ _ _ hdiv _ _ _ _ _ _ ih => exact ih (dvd_add heven hdiv)

inductive FWUpperStageKind where
  | w1 : FWUpperStageKind
  | wheel : Fin 8 → FWUpperStageKind
  | bt : ℕ → FWUpperStageKind
  deriving DecidableEq

structure FWBandConfig where
  m0Num : ℕ
  m0Den : ℕ
  qDen : ℕ
  w1EtaNum : ℕ
  w1EtaDen : ℕ
  w1Steps : ℕ
  rateDen : ℕ
  aInt : ℕ
  bInt : ℕ
  wheelSteps : Fin 8 → ℕ
  btEtaNum : ℕ
  btEtaDen : ℕ
  btProdNum : ℕ
  btProdDen : ℕ
  bt15Steps : ℕ
  bt16Steps : ℕ
  bt17Steps : ℕ

def FWBandConfig.schedule (cfg : FWBandConfig) : List FWUpperStageKind :=
  List.replicate cfg.w1Steps .w1 ++
  (List.finRange 8).flatMap (fun i => List.replicate (cfg.wheelSteps i) (.wheel i)) ++
  List.replicate cfg.bt15Steps (.bt 15) ++
  List.replicate cfg.bt16Steps (.bt 16) ++
  List.replicate cfg.bt17Steps (.bt 17)

def FWBandConfig.w1Count (cfg : FWBandConfig) (j R : ℕ) : ℕ :=
  max 1 ((2 * cfg.w1EtaNum * (cfg.m0Num * cfg.qDen - 2 * cfg.m0Den * j) * R +
    cfg.w1EtaDen * cfg.m0Den * cfg.qDen) / (2 * cfg.w1EtaDen * cfg.m0Den * cfg.qDen))

def FWBandConfig.w1Window (cfg : FWBandConfig) (j R : ℕ) : ℕ :=
  let q := cfg.w1Count j R
  max (fwWheel105Cutoff (q - 1)) ((1001 * q - 6718 + 383) / 384)

def FWBandConfig.w1Step (cfg : FWBandConfig) (j R : ℕ) : ℕ :=
  R + 2 * min (cfg.w1Window j R) (R / 2)

def FWBandConfig.wheelCount (cfg : FWBandConfig) (i : Fin 8) (j R : ℕ) : ℕ :=
  let e := fwEnhancedErrDen i
  let c := fwEnhancedErrNum i
  let p := fwEnhancedRhoNum i
  let q := fwEnhancedRhoDen i
  let rate := cfg.aInt - cfg.bInt * j
  (q * (2 * e * rate * R - cfg.rateDen * (e + 2 * c))) / (2 * cfg.rateDen * e * p)

def FWBandConfig.btCount (cfg : FWBandConfig) (ell R : ℕ) : ℕ :=
  (ell * (2 * cfg.btProdNum * R - cfg.btProdDen)) / (8 * cfg.btProdDen)

def FWBandConfig.stepRadius (cfg : FWBandConfig) (kind : FWUpperStageKind) (j R : ℕ) : ℕ :=
  match kind with
  | .w1 => cfg.w1Step j R
  | .wheel i => R + 2 * cfg.wheelCount i j R
  | .bt ell => R + 2 * cfg.btCount ell R

def FWBandConfig.detRadiusAux (cfg : FWBandConfig) : List FWUpperStageKind → ℕ → ℕ → ℕ
  | [], _, R => R
  | kind :: rest, j, R => cfg.detRadiusAux rest (j + 1) (cfg.stepRadius kind j R)

def FWBandConfig.detRadiusAt (cfg : FWBandConfig) (k : ℕ) : ℕ :=
  cfg.detRadiusAux (cfg.schedule.take k) 0 32

def FWBandConfig.stepGateBool (cfg : FWBandConfig) (kind : FWUpperStageKind) (j R : ℕ) : Bool :=
  match kind with
  | .w1 =>
      decide (2 * cfg.m0Den * j ≤ cfg.m0Num * cfg.qDen ∧
        cfg.w1EtaDen * cfg.m0Den * cfg.qDen ≤
          2 * cfg.w1EtaNum * (cfg.m0Num * cfg.qDen - 2 * cfg.m0Den * j) * R)
  | .wheel i =>
      decide (cfg.bInt * j ≤ cfg.aInt ∧ 1 ≤ cfg.wheelCount i j R)
  | .bt ell =>
      decide ((ell = 15 ∨ ell = 16 ∨ ell = 17) ∧
        cfg.btProdDen ≤ 2 * cfg.btProdNum * R ∧
        btExpCeil ell ≤ cfg.btCount ell R)

def FWBandConfig.allGatesCheckAux (cfg : FWBandConfig) : List FWUpperStageKind → ℕ → ℕ → Bool
  | [], _, _ => true
  | kind :: rest, j, R =>
      cfg.stepGateBool kind j R && cfg.allGatesCheckAux rest (j + 1) (cfg.stepRadius kind j R)

def FWBandConfig.allGatesCheck (cfg : FWBandConfig) : Bool :=
  cfg.allGatesCheckAux cfg.schedule 0 32

theorem w1Count_mono (cfg : FWBandConfig) (j : ℕ) : Monotone (cfg.w1Count j) := by
  intro a b hab
  unfold FWBandConfig.w1Count
  apply max_le_max_left
  apply Nat.div_le_div_right
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_left _ hab

theorem w1Step_mono (cfg : FWBandConfig) (j : ℕ) : Monotone (cfg.w1Step j) := by
  intro a b hab
  have hq := w1Count_mono cfg j hab
  have hw : cfg.w1Window j a ≤ cfg.w1Window j b := by
    unfold FWBandConfig.w1Window
    apply max_le_max
    · rw [← fw_wheel105_cutoff_eq, ← fw_wheel105_cutoff_eq]
      exact fw_wheel_cutoff_mono 105 (by decide) (Nat.sub_le_sub_right hq 1)
    · apply Nat.div_le_div_right
      have hm := Nat.mul_le_mul_left 1001 hq
      have hs := Nat.sub_le_sub_right hm 6718
      omega
  have hr := Nat.div_le_div_right (c := 2) hab
  have hm := min_le_min hw hr
  unfold FWBandConfig.w1Step
  omega

theorem wheelCount_mono (cfg : FWBandConfig) (i : Fin 8) (j : ℕ) :
    Monotone (cfg.wheelCount i j) := by
  intro a b hab
  unfold FWBandConfig.wheelCount
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_left
  apply Nat.sub_le_sub_right
  exact Nat.mul_le_mul_left _ hab

theorem btCount_mono (cfg : FWBandConfig) (ell : ℕ) : Monotone (cfg.btCount ell) := by
  intro a b hab
  unfold FWBandConfig.btCount
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_left
  apply Nat.sub_le_sub_right
  exact Nat.mul_le_mul_left _ hab

def FWBandConfig.m0 (cfg : FWBandConfig) : ℝ := (cfg.m0Num : ℝ) / cfg.m0Den
def FWBandConfig.qbar (cfg : FWBandConfig) : ℝ := 1 / (cfg.qDen : ℝ)
def FWBandConfig.mu (cfg : FWBandConfig) (j : ℕ) : ℝ := cfg.m0 - 2 * cfg.qbar * j
def FWBandConfig.mfW1 (cfg : FWBandConfig) : ℝ := cfg.m0 - 2 * cfg.qbar * cfg.w1Steps
def FWBandConfig.mf238 (cfg : FWBandConfig) : ℝ := cfg.m0 - 2 * cfg.qbar * 238
def FWBandConfig.w1Eta (cfg : FWBandConfig) : ℝ := (cfg.w1EtaNum : ℝ) / cfg.w1EtaDen
def FWBandConfig.btEta (cfg : FWBandConfig) : ℝ := (cfg.btEtaNum : ℝ) / cfg.btEtaDen

structure FWBandConfigValid (cfg : FWBandConfig) : Prop where
  m0Den_pos : 0 < cfg.m0Den
  qDen_pos : 0 < cfg.qDen
  w1EtaDen_pos : 0 < cfg.w1EtaDen
  rateDen_pos : 0 < cfg.rateDen
  btEtaDen_pos : 0 < cfg.btEtaDen
  btProdDen_pos : 0 < cfg.btProdDen
  sched_len : cfg.schedule.length ≤ 238
  w1Steps_le : cfg.w1Steps ≤ 238
  mf238_pos : 0 < cfg.mf238
  w1_eps_nonneg : 0 ≤ 1 / (2 * (1 + 1 / (23 : ℝ))) - cfg.w1Eta
  w1_quota : 2 * (1 / (2 * (1 + 1 / (23 : ℝ))) - cfg.w1Eta) * cfg.mfW1 ^ 2 ≥ 2 * (6 : ℝ) * cfg.qbar
  w1_prefix : ∀ j < cfg.schedule.length, cfg.schedule[j]? = some .w1 → j < cfg.w1Steps
  wheel_rate_le : ∀ j ≤ 238, cfg.bInt * j ≤ cfg.aInt →
    ((cfg.aInt - cfg.bInt * j : ℕ) : ℝ) / cfg.rateDen ≤
      (23 / 48 : ℝ) * cfg.mu j - (6 * cfg.qbar) / cfg.mu j
  bt_prod_eq : (cfg.btProdNum : ℝ) / cfg.btProdDen = cfg.btEta * cfg.mf238
  bt_eps_nonneg : 0 ≤ 1 / (2 * (1 + 1 / (23 : ℝ))) - cfg.btEta
  bt_quota : 12 * cfg.qbar ≤
    (1 / (2 * (1 + 1 / (23 : ℝ))) - cfg.btEta) * cfg.mf238 ^ 2 * 2
  gates_ok : cfg.allGatesCheck = true

theorem w1_step_cutoff_lower (cfg : FWBandConfig) (hv : FWBandConfigValid cfg)
    {j R : ℕ} (hsub : 2 * cfg.m0Den * j ≤ cfg.m0Num * cfg.qDen) :
    let T := ⌊cfg.w1Eta * cfg.mu j * R - 1 / 2⌋₊
    let cutoff := 2 * min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide))) (R / 2)
    cfg.w1Step j R ≤ R + cutoff := by
  dsimp only
  let A : ℝ := cfg.w1Eta * cfg.mu j * R - 1 / 2
  let T : ℕ := ⌊A⌋₊
  let num := 2 * cfg.w1EtaNum * (cfg.m0Num * cfg.qDen - 2 * cfg.m0Den * j) * R +
    cfg.w1EtaDen * cfg.m0Den * cfg.qDen
  let den := 2 * cfg.w1EtaDen * cfg.m0Den * cfg.qDen
  have hden : 0 < den := by
    dsimp [den]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hv.w1EtaDen_pos) hv.m0Den_pos) hv.qDen_pos
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  have hm0D : (cfg.m0Den : ℝ) ≠ 0 := by exact_mod_cast hv.m0Den_pos.ne'
  have hqD : (cfg.qDen : ℝ) ≠ 0 := by exact_mod_cast hv.qDen_pos.ne'
  have hetaD : (cfg.w1EtaDen : ℝ) ≠ 0 := by exact_mod_cast hv.w1EtaDen_pos.ne'
  have hdiv : ((num / den : ℕ) : ℝ) ≤ (num : ℝ) / den := by
    exact_mod_cast Nat.cast_div_le (α := ℝ) (m := num) (n := den)
  have hid : (num : ℝ) / den = A + 1 := by
    dsimp [num, den, A, FWBandConfig.w1Eta, FWBandConfig.mu, FWBandConfig.m0, FWBandConfig.qbar]
    push_cast
    rw [Nat.cast_sub hsub]
    push_cast
    field_simp
    ring
  have hqA : ((num / den : ℕ) : ℝ) ≤ A + 1 := hdiv.trans_eq hid
  have hqT : cfg.w1Count j R ≤ T + 1 := by
    have h1 : num / den ≤ T + 1 := by
      by_cases hA : 0 ≤ A
      · have hf := Nat.le_floor hqA
        rw [Nat.floor_add_one hA] at hf
        exact hf
      · have hlt : ((num / den : ℕ) : ℝ) < 1 := by linarith
        have hnat : num / den < 1 := by exact_mod_cast hlt
        omega
    unfold FWBandConfig.w1Count
    exact max_le (by omega) h1
  have hqminus : cfg.w1Count j R - 1 ≤ T := by omega
  let k := fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
    (Nat.totient_pos.mpr (by decide))
  have h15mono := fw_wheel_cutoff_mono 105 (by decide) hqminus
  have h15W := fw_subwheel_cutoff_le 105 15015 T (by decide) (by decide) (by decide)
  have hdisc : 1001 * (T + 1) ≤ 384 * k + 6718 := fw_base_wheel_cutoff_discrepancy T
  have hbound1 : fwWheel105Cutoff (cfg.w1Count j R - 1) ≤ k := by
    rw [← fw_wheel105_cutoff_eq]
    exact h15mono.trans h15W
  have hbound2 : (1001 * cfg.w1Count j R - 6718 + 383) / 384 ≤ k := by omega
  have hwin : cfg.w1Window j R ≤ k := max_le hbound1 hbound2
  have hm := min_le_min_right (R / 2) hwin
  unfold FWBandConfig.w1Step
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm) R

theorem wheel_count_le_floor_half (cfg : FWBandConfig) (hv : FWBandConfigValid cfg)
    (i : Fin 8) {j R : ℕ} (hj : j ≤ 238) (hsub : cfg.bInt * j ≤ cfg.aInt) :
    cfg.wheelCount i j R ≤
      ⌊fwAffineUniformStockThreshold (cfg.mu j) (6 * cfg.qbar) R (23 / 48)
        (fwMixedWheelRho i) (fwMixedWheelError i) / 2⌋₊ := by
  let p := fwEnhancedRhoNum i
  let q := fwEnhancedRhoDen i
  let c := fwEnhancedErrNum i
  let e := fwEnhancedErrDen i
  let a := cfg.aInt - cfg.bInt * j
  let P := 2 * e * a * R
  let N := cfg.rateDen * (e + 2 * c)
  let den := 2 * cfg.rateDen * e * p
  obtain ⟨hp, hq, he, hrho, herr⟩ := fw_enhanced_wheel_rationals i
  have hden : 0 < den :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hv.rateDen_pos) he) hp
  by_cases hPN : N ≤ P
  · have hdiv : ((q * (P - N) / den : ℕ) : ℝ) ≤ (q * (P - N) : ℕ) / (den : ℝ) := by
      exact_mod_cast Nat.cast_div_le (α := ℝ) (m := q * (P - N)) (n := den)
    have hsubPN : ((P - N : ℕ) : ℝ) = (P : ℝ) - N := Nat.cast_sub hPN
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp
    have hepos : (0 : ℝ) < e := by exact_mod_cast he
    have hrpos : (0 : ℝ) < cfg.rateDen := by exact_mod_cast hv.rateDen_pos
    have hiden : ((q * (P - N) : ℕ) : ℝ) / den =
        (((a : ℝ) / cfg.rateDen) * R - (1 / 2 + (c : ℝ) / e)) / ((p : ℝ) / q) := by
      push_cast
      rw [hsubPN]
      dsimp [P, N, den]
      push_cast
      field_simp
    have hrate := hv.wheel_rate_le j hj hsub
    have hR : (0 : ℝ) ≤ R := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hrate hR
    have hreal : ((q * (P - N) / den : ℕ) : ℝ) ≤
        fwAffineUniformStockThreshold (cfg.mu j) (6 * cfg.qbar) R (23 / 48)
          (fwMixedWheelRho i) (fwMixedWheelError i) / 2 := by
      rw [hiden] at hdiv
      unfold fwAffineUniformStockThreshold
      rw [hrho, herr]
      dsimp [p, q, c, e, a] at *
      have hm := div_le_div_of_nonneg_right
        (show (((cfg.aInt - cfg.bInt * j : ℕ) : ℝ) / cfg.rateDen) * R -
            (1 / 2 + (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i) ≤
          ((23 / 48 : ℝ) * cfg.mu j - (6 * cfg.qbar) / cfg.mu j) * R -
            (1 / 2 + (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i) by linarith)
        (show 0 ≤ ((fwEnhancedRhoNum i : ℝ) / fwEnhancedRhoDen i) by positivity)
      have hn : (2 / ((fwEnhancedRhoNum i : ℝ) / fwEnhancedRhoDen i)) *
          (((23 / 48 : ℝ) * cfg.mu j - (6 * cfg.qbar) / cfg.mu j) * R -
            (1 / 2 + (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i)) / 2 =
          (((23 / 48 : ℝ) * cfg.mu j - (6 * cfg.qbar) / cfg.mu j) * R -
            (1 / 2 + (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i)) /
            ((fwEnhancedRhoNum i : ℝ) / fwEnhancedRhoDen i) := by ring
      rw [hn]
      exact hdiv.trans hm
    change q * (P - N) / den ≤ _
    exact Nat.le_floor hreal
  · have hz : P - N = 0 := Nat.sub_eq_zero_of_le (by omega)
    change q * (P - N) / den ≤ _
    simp [hz]

theorem bt_count_le_floor_half (cfg : FWBandConfig) (hv : FWBandConfigValid cfg)
    {ell R : ℕ} (hsub : cfg.btProdDen ≤ 2 * cfg.btProdNum * R) :
    cfg.btCount ell R ≤ ⌊((ell : ℝ) / 2) * (cfg.btEta * cfg.mf238 * R - 1 / 2) / 2⌋₊ := by
  let num := ell * (2 * cfg.btProdNum * R - cfg.btProdDen)
  let den := 8 * cfg.btProdDen
  have hden : 0 < den := Nat.mul_pos (by decide) hv.btProdDen_pos
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  have hprodD : (cfg.btProdDen : ℝ) ≠ 0 := by exact_mod_cast hv.btProdDen_pos.ne'
  have hdiv : ((num / den : ℕ) : ℝ) ≤ (num : ℝ) / den := by
    exact_mod_cast Nat.cast_div_le (α := ℝ) (m := num) (n := den)
  have hid : (num : ℝ) / den = ((ell : ℝ) / 2) * (cfg.btEta * cfg.mf238 * R - 1 / 2) / 2 := by
    rw [← hv.bt_prod_eq]
    dsimp [num, den]
    push_cast
    rw [Nat.cast_sub hsub]
    push_cast
    field_simp
    ring
  exact Nat.le_floor (hdiv.trans_eq hid)

theorem fw_band_crossing_of_config
    (mv : MVBrunTitchmarsh) (cfg : FWBandConfig) (hv : FWBandConfigValid cfg)
    {n : ℕ} (hnlo : 21249 ≤ n)
    (hbase : cfg.m0 * (poolMaximum n : ℝ) ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n)
    (hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ cfg.qbar * (poolMaximum n : ℝ))
    (hcrossDet : (poolMaximum n : ℝ) / 23 ≤ cfg.detRadiusAux cfg.schedule 0 32)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages ∧
      stages.length ≤ 238 ∧
      final ⊆ initial ∧
      final.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      (poolMaximum n : ℝ) / 23 ≤ last ∧
      (last : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
  dsimp only
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  have hn13 : 13 ≤ n * n := by nlinarith
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hqbar_nonneg : 0 ≤ cfg.qbar := by
    unfold FWBandConfig.qbar; positivity
  have hmu_gt_mf238 : ∀ j ≤ 238, cfg.mf238 ≤ cfg.mu j := by
    intro j hj
    unfold FWBandConfig.mf238 FWBandConfig.mu
    have hjR : (j : ℝ) ≤ 238 := by exact_mod_cast hj
    nlinarith
  have hstock_at : ∀ (last : ℕ) (S : Finset ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 S last stages →
      cfg.mu stages.length * (poolMaximum n : ℝ) ≤ (S.card : ℝ) := by
    intro last S stages trace
    have hst := (fw_wheel_witness_trace_stock hn13 batches hvalid candidates hcard kept hsub hkept
      hinj blocks hblocks 32 last S stages trace).2.2.2.1
    have hstR : ((n * n : ℕ) : ℝ) ≤ (S.card : ℝ) + fwEarlyBudget n + 13 +
        2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length := by exact_mod_cast hst
    have hqSteps := mul_le_mul_of_nonneg_left hQ
      (show (0 : ℝ) ≤ 2 * (stages.length : ℝ) by positivity)
    unfold FWBandConfig.mu
    push_cast at *
    nlinarith
  have hreduced : ∀ a ∈ ({1} : Finset ℕ), 0 < a ∧ Nat.Coprime 2 a := by
    intro a ha
    have : a = 1 := by simpa using ha
    subst a; decide
  have hrun : ∀ (rem : List FWUpperStageKind) (j R last : ℕ) (S : Finset ℕ)
      (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 S last stages →
      stages.length = j →
      j + rem.length ≤ 238 →
      (∀ k < rem.length, rem[k]? = some .w1 → j + k < cfg.w1Steps) →
      cfg.allGatesCheckAux rem j R = true →
      32 ≤ R → R ≤ last → 2 ∣ last →
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages →
      (last : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) →
      ∃ (final : Finset ℕ) (last' : ℕ) (stages' : List BTSelectedStage),
        BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last' stages' ∧
        stages'.length ≤ 238 ∧
        NarrowedStages ((poolMaximum n : ℝ) / 6) stages' ∧
        ((poolMaximum n : ℝ) / 23 ≤ last' ∨ cfg.detRadiusAux rem j R ≤ last') ∧
        (last' : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
    intro rem
    induction rem with
    | nil =>
      intro j R last S stages trace hlen hbud _ _ _ hRlast _ hnar hup
      exact ⟨S, last, stages, trace, by omega, hnar, Or.inr hRlast, hup⟩
    | cons kind rest ih =>
      intro j R last S stages trace hlen hbud hw1pre hgates hR32 hRlast heven hnar hup
      by_cases hdone : (poolMaximum n : ℝ) / 23 ≤ last
      · exact ⟨S, last, stages, trace, by omega, hnar, Or.inl hdone, hup⟩
      · have hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / 23 := lt_of_not_ge hdone
        simp only [FWBandConfig.allGatesCheckAux, Bool.and_eq_true] at hgates
        rcases hgates with ⟨hgateStep, hgatesRest⟩
        have hj238 : j ≤ 238 := by simp at hbud; omega
        have hlastPos : 0 < last := by omega
        have hw1Rest : ∀ k < rest.length, rest[k]? = some .w1 → (j + 1) + k < cfg.w1Steps := by
          intro k hk hsome
          have hk' : k + 1 < (kind :: rest).length := by simp; omega
          have hsome' : (kind :: rest)[k + 1]? = some .w1 := by simpa using hsome
          have := hw1pre (k + 1) hk' hsome'
          omega
        cases kind with
        | w1 =>
          have hjw1 : j < cfg.w1Steps := hw1pre 0 (by simp) rfl
          simp only [FWBandConfig.stepGateBool, decide_eq_true_eq] at hgateStep
          rcases hgateStep with ⟨hsubStep, hAint⟩
          have hmfW1_nonneg : 0 ≤ cfg.mfW1 := by
            have := hv.mf238_pos
            have : cfg.mf238 ≤ cfg.mfW1 := by
              unfold FWBandConfig.mf238 FWBandConfig.mfW1
              have hw1le : (cfg.w1Steps : ℝ) ≤ 238 := by exact_mod_cast hv.w1Steps_le
              nlinarith
            linarith
          have hm_ge_mf : cfg.mfW1 ≤ cfg.mu j := by
            unfold FWBandConfig.mfW1 FWBandConfig.mu
            have hjR : (j : ℝ) ≤ cfg.w1Steps := by exact_mod_cast hjw1.le
            nlinarith
          have hmBound : cfg.mu j ≤ (((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n -
              2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length) / (poolMaximum n : ℝ) := by
            rw [le_div_iff₀ hX, hlen]
            have hqSteps := mul_le_mul_of_nonneg_left hQ
              (show (0 : ℝ) ≤ 2 * (j : ℝ) by positivity)
            unfold FWBandConfig.mu
            nlinarith
          have hAR : 0 ≤ cfg.w1Eta * cfg.mu j * R - 1 / 2 := by
            have hm0D : (0 : ℝ) < cfg.m0Den := by exact_mod_cast hv.m0Den_pos
            have hqD : (0 : ℝ) < cfg.qDen := by exact_mod_cast hv.qDen_pos
            have hetaD : (0 : ℝ) < cfg.w1EtaDen := by exact_mod_cast hv.w1EtaDen_pos
            have hdenPos : (0 : ℝ) < 2 * cfg.w1EtaDen * cfg.m0Den * cfg.qDen := by positivity
            have hAintR : ((cfg.w1EtaDen * cfg.m0Den * cfg.qDen : ℕ) : ℝ) ≤
                ((2 * cfg.w1EtaNum * (cfg.m0Num * cfg.qDen - 2 * cfg.m0Den * j) * R : ℕ) : ℝ) := by
              exact_mod_cast hAint
            have hid : cfg.w1Eta * cfg.mu j * R - 1 / 2 =
                (((2 * cfg.w1EtaNum * (cfg.m0Num * cfg.qDen - 2 * cfg.m0Den * j) * R : ℕ) : ℝ) -
                  ((cfg.w1EtaDen * cfg.m0Den * cfg.qDen : ℕ) : ℝ)) /
                (2 * cfg.w1EtaDen * cfg.m0Den * cfg.qDen) := by
              unfold FWBandConfig.w1Eta FWBandConfig.mu FWBandConfig.m0 FWBandConfig.qbar
              push_cast
              rw [Nat.cast_sub hsubStep]
              push_cast
              field_simp
            rw [hid]
            exact div_nonneg (by linarith) hdenPos.le
          have hAlast : 0 ≤ cfg.w1Eta * cfg.mu j * last - 1 / 2 := by
            have hmu_nonneg : 0 ≤ cfg.mu j := le_trans hmfW1_nonneg hm_ge_mf
            have heta_nonneg : 0 ≤ cfg.w1Eta := by unfold FWBandConfig.w1Eta; positivity
            have hRle : (R : ℝ) ≤ last := by exact_mod_cast hRlast
            have hmul := mul_le_mul_of_nonneg_left hRle (mul_nonneg heta_nonneg hmu_nonneg)
            linarith
          have heta_nonneg : 0 ≤ cfg.w1Eta := by unfold FWBandConfig.w1Eta; positivity
          obtain ⟨gap, chosen, hgap, hdiv, hcut, hmax, _, _, _, _, _, _, _, hmid, hrad, htrace⟩ :=
            fw_wheel_trace_first_window_append hn13 batches hvalid candidates hcard kept hsub hkept
              hinj blocks hblocks 32 last S stages trace last 23 (cfg.mu j) cfg.mfW1 cfg.w1Eta
              cfg.qbar hlastPos heven le_rfl (by norm_num) hnotdone hmfW1_nonneg hm_ge_mf
              heta_nonneg hv.w1_eps_nonneg hmBound hAlast hQ hv.w1_quota
          have hstep1 : cfg.w1Step j R ≤ cfg.w1Step j last := w1Step_mono cfg j hRlast
          have hstep2 := w1_step_cutoff_lower cfg hv (R := last) hsubStep
          have hnextR : cfg.w1Step j R ≤ last + gap :=
            hstep1.trans (hstep2.trans hrad)
          have hnext32 : 32 ≤ cfg.w1Step j R := by
            unfold FWBandConfig.w1Step; omega
          have hup' : ((last + gap : ℕ) : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
            have hgapR : (gap : ℝ) ≤ last := by exact_mod_cast hmax
            have : ((last + gap : ℕ) : ℝ) ≤ 2 * ((poolMaximum n : ℝ) / 23) := by
              push_cast; linarith
            exact this.trans (le_max_right _ _)
          refine ih (j + 1) (cfg.w1Step j R) (last + gap) (S \ pairFootprint chosen gap)
            _ htrace (by rw [List.length_append, List.length_singleton, hlen])
            (by rw [List.length_cons] at hbud; omega)
            hw1Rest hgatesRest hnext32 hnextR (dvd_add heven hdiv) ?_ hup'
          intro s hs p hp q hq
          rcases List.mem_append.mp hs with hs | hs
          · exact hnar s hs p hp q hq
          · rw [List.mem_singleton.mp hs] at hp hq ⊢
            exact hmid p hp q hq
        | wheel i =>
          simp only [FWBandConfig.stepGateBool, decide_eq_true_eq] at hgateStep
          rcases hgateStep with ⟨hsubStep, hcnt1⟩
          have hcntLast : 1 ≤ cfg.wheelCount i j last :=
            hcnt1.trans (wheelCount_mono cfg i j hRlast)
          have hfloorHalf := wheel_count_le_floor_half cfg hv i hj238 hsubStep (R := last)
          let D := fwAffineUniformStockThreshold (cfg.mu j) (6 * cfg.qbar) last (23 / 48)
            (fwMixedWheelRho i) (fwMixedWheelError i)
          have hfloor1 : 1 ≤ ⌊D / 2⌋₊ := hcntLast.trans hfloorHalf
          have hDpos : 0 < D := by
            by_contra hle
            have : ⌊D / 2⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
            omega
          have hpool : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
            trace.final_accounting.1.trans Finset.sdiff_subset
          have hS : ∀ p ∈ S, (p : ℝ) ≤ poolMaximum n ∧ p % 2 = 1 ∧
              Nat.Coprime p (fwMixedWheel i) := by
            intro p hp
            have hp' := fw_screened_pool_mixed_wheel_units hpool p hp
            exact ⟨by exact_mod_cast pool_le_poolMaximum hp'.1, hp'.2.2.1, hp'.2.2.2 i⟩
          have hstock := hlen ▸ hstock_at last S stages trace
          have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) ≤ (6 * cfg.qbar) * (poolMaximum n : ℝ) := by
            have h := mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ 6 by norm_num)
            push_cast at h ⊢; linarith
          have hmuPos : 0 < cfg.mu j := lt_of_lt_of_le hv.mf238_pos (hmu_gt_mf238 j hj238)
          have hc0 : (1 / (2 * (1 + 1 / (23 : ℝ))) : ℝ) = 23 / 48 := by norm_num
          obtain ⟨gap, cands, hgap, hdiv, hmin, hmax, hcardC, _, havail, hmatching⟩ :=
            fw_affine_uniform_stock_common_gap S (fwMixedWheel i) last 6 (6 * (n + 8))
              (poolMaximum n) 23 (fwMixedWheelRho i) (fwMixedWheelError i)
              (cfg.mu j) (6 * cfg.qbar)
              (fw_mixed_wheel_pos_odd i).2 hlastPos heven (by omega) hX (by norm_num)
              hnotdone.le hS (fw_mixed_wheel_rho_pos i) (fw_mixed_wheel_affine_discrepancy i)
              hmuPos (by positivity) hstock hquota (by rw [hc0]; exact hDpos)
          rw [hc0] at hmin
          have hfootC : pairFootprint cands gap ⊆ S := by
            intro p hp
            rcases Finset.mem_union.mp hp with hp | hp
            · exact (havail p hp).1
            · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
              exact (havail q hq).2
          have hspan : ∀ p ∈ cands, (0 : ℝ) ≤ p ∧
              (p : ℝ) < 0 + (6 : ℕ) * ((poolMaximum n : ℝ) / 6) := by
            intro p hp
            have hbound := (hS (p + gap) (havail p hp).2).1
            have hgap' : (0 : ℝ) < gap := by exact_mod_cast hgap
            push_cast at hbound
            constructor <;> linarith
          obtain ⟨chosen, _, _, _, _, _, _, hmid, htrace⟩ :=
            trace.append_narrow_matching (z := 6) cands gap D 0 ((poolMaximum n : ℝ) / 6)
              hgap hdiv hmax hmin (by decide) (by positivity) hspan hcardC hmatching hfootC
          have hgapInc : 2 * cfg.wheelCount i j R ≤ gap := by
            have h1 : cfg.wheelCount i j R ≤ ⌊D / 2⌋₊ :=
              (wheelCount_mono cfg i j hRlast).trans hfloorHalf
            exact (Nat.mul_le_mul_left 2 h1).trans (even_gap_ge_two_mul_floor_half hdiv hmin)
          have hnextR : R + 2 * cfg.wheelCount i j R ≤ last + gap := Nat.add_le_add hRlast hgapInc
          have hnar' : NarrowedStages ((poolMaximum n : ℝ) / 6)
              (stages ++ [⟨gap, chosen, D⟩]) := by
            intro s hs p hp q hq
            rcases List.mem_append.mp hs with hs | hs
            · exact hnar s hs p hp q hq
            · simp only [List.mem_singleton] at hs
              subst hs
              exact hmid p hp q hq
          have hup' : ((last + gap : ℕ) : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
            have hgapR : (gap : ℝ) ≤ last := by exact_mod_cast hmax
            have : ((last + gap : ℕ) : ℝ) ≤ 2 * ((poolMaximum n : ℝ) / 23) := by
              push_cast; linarith
            exact this.trans (le_max_right _ _)
          exact ih (j + 1) (R + 2 * cfg.wheelCount i j R) (last + gap)
            (S \ pairFootprint chosen gap) (stages ++ [⟨gap, chosen, D⟩]) htrace
            (by rw [List.length_append, List.length_singleton, hlen])
            (by rw [List.length_cons] at hbud; omega) hw1Rest hgatesRest
            (by omega) hnextR (dvd_add heven hdiv) hnar' hup'
        | bt ell =>
          simp only [FWBandConfig.stepGateBool, decide_eq_true_eq] at hgateStep
          rcases hgateStep with ⟨hell, hsubR, hexpCnt⟩
          have hsubLast : cfg.btProdDen ≤ 2 * cfg.btProdNum * last :=
            hsubR.trans (Nat.mul_le_mul_left _ hRlast)
          let D : ℝ := ((ell : ℝ) / 2) * (cfg.btEta * cfg.mf238 * last - 1 / 2)
          have hfloorHalf := bt_count_le_floor_half cfg hv (ell := ell) hsubLast
          have hcntLast : btExpCeil ell ≤ cfg.btCount ell last :=
            hexpCnt.trans (btCount_mono cfg ell hRlast)
          have hfloorExp : btExpCeil ell ≤ ⌊D / 2⌋₊ := hcntLast.trans hfloorHalf
          have hceilGe2 : 2 ≤ btExpCeil ell := by
            rcases hell with rfl | rfl | rfl <;> decide
          have hDhalfGe : (btExpCeil ell : ℝ) ≤ D / 2 := by
            have hpos : 0 ≤ D / 2 := by
              by_contra hle
              have : ⌊D / 2⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hle)
              omega
            exact (Nat.le_floor_iff hpos).mp hfloorExp
          have hexp : Real.exp (ell : ℝ) ≤ D / 2 :=
            (exp_le_btExpCeil hell).trans hDhalfGe
          have hDgt2 : (2 : ℝ) < D := by
            have : (2 : ℝ) ≤ btExpCeil ell := by exact_mod_cast hceilGe2
            linarith
          have hellPos : (0 : ℝ) < ell := by
            rcases hell with rfl | rfl | rfl <;> norm_num
          let M : ℝ := cfg.mf238 * (poolMaximum n : ℝ)
          have hMnonneg : 0 ≤ M := mul_nonneg hv.mf238_pos.le hX.le
          have hstockMu := hlen ▸ hstock_at last S stages trace
          have hstockM : M ≤ (S.card : ℝ) :=
            (mul_le_mul_of_nonneg_right (hmu_gt_mf238 j hj238) hX.le).trans hstockMu
          have hSne : S.Nonempty := by
            apply Finset.card_pos.mp
            have hpos : (0 : ℝ) < S.card := lt_of_lt_of_le (mul_pos hv.mf238_pos hX) hstockM
            exact_mod_cast hpos
          have hpool : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
            trace.final_accounting.1.trans Finset.sdiff_subset
          have hunits := fw_screened_pool_mixed_wheel_units hpool
          have hprimes : ∀ p ∈ S, Nat.Prime p := fun p hp => (pool_prime_and_residue (hunits p hp).1).1
          have hclasses : ∀ p ∈ S, p % 2 ∈ ({1} : Finset ℕ) := by
            intro p hp; simpa using (hunits p hp).2.2.1
          have hcapX : ∀ p ∈ S, (p : ℝ) ≤ poolMaximum n := by
            intro p hp; exact_mod_cast pool_le_poolMaximum (hunits p hp).1
          have hwidthEq : D = ((ell : ℝ) * (Nat.totient 2 : ℝ) / (2 * (2 : ℕ))) * (2 : ℕ) *
              (cfg.btEta * M * last / (1 * (poolMaximum n : ℝ)) - 1 / 2) := by
            dsimp [D, M]
            have hXne : (poolMaximum n : ℝ) ≠ 0 := hX.ne'
            norm_num
            field_simp
            ring
          have hbtEta_nonneg : 0 ≤ cfg.btEta := by unfold FWBandConfig.btEta; positivity
          have hbudget : 2 * ((6 * (6 * (n + 8)) : ℕ) : ℝ) * 1 * (poolMaximum n : ℝ) ≤
              (1 / (2 * (1 + 1 / (23 : ℝ))) - cfg.btEta) * M ^ 2 * (2 : ℕ) := by
            have hQX := mul_le_mul_of_nonneg_right hQ hX.le
            have hq2 := mul_le_mul_of_nonneg_right hv.bt_quota (sq_nonneg (poolMaximum n : ℝ))
            have hpow : (cfg.mf238 * (poolMaximum n : ℝ)) ^ 2 = cfg.mf238 ^ 2 * (poolMaximum n : ℝ) ^ 2 :=
              mul_pow _ _ 2
            dsimp [M]
            rw [hpow]
            push_cast at hQX ⊢
            nlinarith
          have hlastR : (0 : ℝ) < last := by exact_mod_cast hlastPos
          have hgate := bt_source_implies_exact_bin_gate S ({1} : Finset ℕ) 1 (poolMaximum n)
            1 last 23 cfg.btEta M ell D 2 (6 * (6 * (n + 8))) hMnonneg hstockM (by norm_num) hX
            (by norm_num) hlastR (by norm_num) (by decide) hellPos (by decide) (by norm_num)
            hbtEta_nonneg hv.bt_eps_nonneg hnotdone.le hwidthEq hbudget
          have hgate' : (((⌊(last : ℝ)⌋₊ / 2) * (2 * (6 * (6 * (n + 8)))) : ℕ) : ℝ) +
              (S.card : ℝ) * (2 * D / ((Nat.totient 2 : ℝ) * ell)) ≤
              ((S.card : ℝ) ^ 2 / ((⌊(poolMaximum n : ℝ) / (last : ℝ)⌋₊ + 1) * ({1} : Finset ℕ).card : ℕ) -
                S.card) / 2 := by
            simpa using hgate
          have hinterval : ∀ p ∈ S, (0 : ℝ) ≤ p ∧ (p : ℝ) ≤ 0 + poolMaximum n :=
            fun p hp => ⟨by positivity, by simpa using hcapX p hp⟩
          have hcapMid : ∀ p ∈ S, (p : ℝ) ≤ 6 * ((poolMaximum n : ℝ) / 6) := by
            intro p hp; linarith [hcapX p hp]
          obtain ⟨gap, _, chosen, hgap, hdiv, hmax, hmin, _, _, _, _, _, _, _, _, _, hmid, htrace⟩ :=
            trace.append_bt_six_narrow_matching mv ({1} : Finset ℕ) 0 (poolMaximum n) D ell
              ((poolMaximum n : ℝ) / 6) last hSne hprimes hinterval hclasses hreduced
              hlastPos le_rfl hDgt2 hellPos hexp hgate' (by positivity) hcapMid
          have hgapInc : 2 * cfg.btCount ell R ≤ gap := by
            have h1 : cfg.btCount ell R ≤ ⌊D / 2⌋₊ :=
              (btCount_mono cfg ell hRlast).trans hfloorHalf
            exact (Nat.mul_le_mul_left 2 h1).trans (even_gap_ge_two_mul_floor_half hdiv hmin)
          have hnextR : R + 2 * cfg.btCount ell R ≤ last + gap := Nat.add_le_add hRlast hgapInc
          have hnar' : NarrowedStages ((poolMaximum n : ℝ) / 6)
              (stages ++ [⟨gap, chosen, D⟩]) := by
            intro s hs p hp q hq
            rcases List.mem_append.mp hs with hs | hs
            · exact hnar s hs p hp q hq
            · simp only [List.mem_singleton] at hs
              subst hs
              exact hmid p hp q hq
          have hup' : ((last + gap : ℕ) : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
            have hgapR : (gap : ℝ) ≤ last := by exact_mod_cast hmax
            have : ((last + gap : ℕ) : ℝ) ≤ 2 * ((poolMaximum n : ℝ) / 23) := by
              push_cast; linarith
            exact this.trans (le_max_right _ _)
          exact ih (j + 1) (R + 2 * cfg.btCount ell R) (last + gap)
            (S \ pairFootprint chosen gap) (stages ++ [⟨gap, chosen, D⟩]) htrace
            (by rw [List.length_append, List.length_singleton, hlen])
            (by rw [List.length_cons] at hbud; omega) hw1Rest hgatesRest
            (by omega) hnextR (dvd_add heven hdiv) hnar' hup'
  obtain ⟨final, last, stages, htrace, hlen, hnar, hstop, hup⟩ :=
    hrun cfg.schedule 0 32 32 initial [] (BTGrowingTrace.nil _ _) rfl
      (by simpa using hv.sched_len) (by intro k hk hs; simpa using hv.w1_prefix k hk hs)
      hv.gates_ok le_rfl le_rfl (by decide) (by simp [NarrowedStages]) (le_max_left _ _)
  have hcross : (poolMaximum n : ℝ) / 23 ≤ last := by
    rcases hstop with h | h
    · exact h
    · exact hcrossDet.trans (by exact_mod_cast h)
  have havoid : ∀ stage ∈ stages, Disjoint stage.footprint
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    intro stage hs
    apply Finset.disjoint_left.mpr
    intro p hp hearly
    exact (Finset.mem_sdiff.mp (htrace.footprints_subset stage hs hp)).2 hearly
  exact ⟨final, last, stages, htrace, hlen, htrace.final_accounting.1,
    htrace.final_accounting.2.1, htrace.pairwise_disjoint, hnar, havoid, hcross, hup⟩

/-! ### Band A (`21249 ≤ n ≤ 27554`) -/

def fwBandAConfig : FWBandConfig where
  m0Num := 395
  m0Den := 10000
  qDen := 76700
  w1EtaNum := 4194
  w1EtaDen := 10000
  w1Steps := 116
  rateDen := 1000000000000
  aInt := 16577505278
  bInt := 12494568
  wheelSteps := ![6, 11, 11, 9, 10, 9, 9, 34]
  btEtaNum := 4069
  btEtaDen := 10000
  btProdNum := 15985849
  btProdDen := 1180000000
  bt15Steps := 9
  bt16Steps := 9
  bt17Steps := 5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fwBandA_gates_ok : fwBandAConfig.allGatesCheck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fwBandA_det_final :
    844611524 ≤ fwBandAConfig.detRadiusAux fwBandAConfig.schedule 0 32 := by decide +kernel

theorem fwBandAConfig_valid : FWBandConfigValid fwBandAConfig where
  m0Den_pos := by decide
  qDen_pos := by decide
  w1EtaDen_pos := by decide
  rateDen_pos := by decide
  btEtaDen_pos := by decide
  btProdDen_pos := by decide
  sched_len := by decide +kernel
  w1Steps_le := by decide
  mf238_pos := by
    unfold FWBandConfig.mf238 FWBandConfig.m0 FWBandConfig.qbar fwBandAConfig
    norm_num
  w1_eps_nonneg := by
    unfold FWBandConfig.w1Eta fwBandAConfig
    norm_num
  w1_quota := by
    unfold FWBandConfig.w1Eta FWBandConfig.mfW1 FWBandConfig.m0 FWBandConfig.qbar fwBandAConfig
    norm_num
  w1_prefix := by
    have hdec : ∀ j : Fin fwBandAConfig.schedule.length,
        fwBandAConfig.schedule[j.val]? = some .w1 → j.val < fwBandAConfig.w1Steps := by
      decide +kernel
    intro j hj hs
    exact hdec ⟨j, hj⟩ hs
  wheel_rate_le := by
    intro j hj hsub
    have hmu : (51073 / 1534000 : ℝ) ≤ fwBandAConfig.mu j := by
      unfold FWBandConfig.mu FWBandConfig.m0 FWBandConfig.qbar fwBandAConfig
      have hjR : (j : ℝ) ≤ 238 := by exact_mod_cast hj
      norm_num
      linarith
    have hdiv : (6 * fwBandAConfig.qbar) / fwBandAConfig.mu j ≤
        (6 * fwBandAConfig.qbar) / (51073 / 1534000) := by
      unfold FWBandConfig.qbar fwBandAConfig
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmu
    rw [Nat.cast_sub hsub]
    unfold FWBandConfig.mu FWBandConfig.m0 FWBandConfig.qbar fwBandAConfig at hdiv ⊢
    push_cast
    norm_num at hdiv ⊢
    linarith
  bt_prod_eq := by
    unfold FWBandConfig.btEta FWBandConfig.mf238 FWBandConfig.m0 FWBandConfig.qbar fwBandAConfig
    norm_num
  bt_eps_nonneg := by
    unfold FWBandConfig.btEta fwBandAConfig
    norm_num
  bt_quota := by
    dsimp [FWBandConfig.qbar, FWBandConfig.btEta, FWBandConfig.mf238, FWBandConfig.m0, fwBandAConfig]
    norm_num
  gates_ok := fwBandA_gates_ok

theorem fwBandA_envelopes
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 21249 ≤ n) (hnhi : n ≤ 27554) :
    (poolMaximum n : ℝ) ≤ (22974 / 1000 : ℝ) * (n : ℝ) ^ 2 ∧
    fwBandAConfig.m0 * (poolMaximum n : ℝ) ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n ∧
    ((6 * (n + 8) : ℕ) : ℝ) ≤ fwBandAConfig.qbar * (poolMaximum n : ℝ) := by
  have hnloR : (21249 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hnhiR : (n : ℝ) ≤ 27554 := by exact_mod_cast hnhi
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjone : 1 < j := by dsimp [j]; push_cast; nlinarith
  have hjhi : j ≤ 759222917 := by dsimp [j]; push_cast; nlinarith
  have hlogj : Real.log j < 225 / 11 := by
    have h1 := Real.log_le_log hjpos hjhi
    have h2 : Real.log (759222917 : ℝ) < (225 : ℝ) / 11 :=
      log_lt_of_pow_lt_exp 759222917 225 11 (by norm_num) (by decide) (by norm_num)
    linarith
  have hlog225 : Real.log (225 / 11 : ℝ) < 163 / 54 :=
    log_lt_of_pow_lt_exp (225 / 11) 163 54 (by norm_num) (by decide) (by norm_num)
  have hloglogj : Real.log (Real.log j) < 163 / 54 :=
    lt_of_le_of_lt (Real.log_le_log (Real.log_pos hjone) hlogj.le) hlog225
  have hfactor : Real.log j + Real.log (Real.log j) - 1 / 2 < 6823 / 297 := by linarith
  have hu := poolMaximum_upper_sharp upperSharp n (by nlinarith)
  change (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j) - 1 / 2) at hu
  have hprod := mul_lt_mul_of_pos_left hfactor hjpos
  have hXup : (poolMaximum n : ℝ) ≤ (22974 / 1000 : ℝ) * (n : ℝ) ^ 2 := by
    dsimp [j] at hu hprod
    push_cast at hu hprod
    nlinarith
  have hearly : (fwEarlyBudget n : ℝ) ≤ (92 / 1000 : ℝ) * (n : ℝ) ^ 2 := by
    have hdiv : ((n / 450 : ℕ) : ℝ) * 450 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 450
    dsimp [fwEarlyBudget]
    push_cast
    have h1 : (n : ℝ) + 8 ≤ (2657 / 2656 : ℝ) * n := by linarith
    have h2 : 21 + 3 * ((n / 450 : ℕ) : ℝ) ≤ (46 / 6000 : ℝ) * n := by linarith
    have hp := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith
  have hbase : fwBandAConfig.m0 * (poolMaximum n : ℝ) ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n := by
    unfold FWBandConfig.m0 fwBandAConfig
    have hsq : (100000 : ℝ) * 13 ≤ (n : ℝ) ^ 2 := by nlinarith
    push_cast
    nlinarith
  have hjlo : (451520002 : ℝ) ≤ j := by dsimp [j]; push_cast; nlinarith
  have hlogj_lo : (19 : ℝ) < Real.log j := by
    have h1 := lt_log_of_exp_lt_pow 451520002 19 1 (by norm_num) (by decide) (by norm_num)
    norm_num at h1
    have h2 := Real.log_le_log (by norm_num) hjlo
    linarith
  have hXlo_raw := poolMaximum_lower lower n
  change j * Real.log j < (poolMaximum n : ℝ) at hXlo_raw
  have hXlo : (8578880038 : ℝ) < poolMaximum n := by nlinarith
  have hlogX : (114 / 5 : ℝ) < Real.log (poolMaximum n : ℝ) := by
    have h1 : (114 : ℝ) / 5 < Real.log (8578880038 : ℝ) :=
      lt_log_of_exp_lt_pow 8578880038 114 5 (by norm_num) (by decide) (by norm_num)
    have h2 := Real.log_le_log (by norm_num) hXlo.le
    linarith
  have hratio := fw_actual_index_ratio_of_theta (n := n) bmor lower upper (by omega) (by omega)
  have hXfw3 : (867 / 40 : ℝ) * (n : ℝ) ^ 2 < poolMaximum n := by
    have hsq : 0 < (n : ℝ) ^ 2 := by positivity
    exact (lt_div_iff₀ hsq).mp (by linarith)
  have hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ fwBandAConfig.qbar * (poolMaximum n : ℝ) := by
    unfold FWBandConfig.qbar fwBandAConfig
    push_cast
    nlinarith
  exact ⟨hXup, hbase, hQ⟩

/-! ### Band B (`27555 ≤ n ≤ 35733`) -/

def fwBandBConfig : FWBandConfig where
  m0Num := 385
  m0Den := 10000
  qDen := 101800
  w1EtaNum := 4336
  w1EtaDen := 10000
  w1Steps := 114
  rateDen := 1000000000000
  aInt := 16705402218
  bInt := 9413884
  wheelSteps := ![6, 11, 11, 9, 10, 9, 9, 31]
  btEtaNum := 4271
  btEtaDen := 10000
  btProdNum := 147063343
  btProdDen := 10180000000
  bt15Steps := 9
  bt16Steps := 9
  bt17Steps := 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fwBandB_gates_ok : fwBandBConfig.allGatesCheck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fwBandB_det_final :
    1627156628 ≤ fwBandBConfig.detRadiusAux fwBandBConfig.schedule 0 32 := by decide +kernel

theorem fwBandBConfig_valid : FWBandConfigValid fwBandBConfig where
  m0Den_pos := by decide
  qDen_pos := by decide
  w1EtaDen_pos := by decide
  rateDen_pos := by decide
  btEtaDen_pos := by decide
  btProdDen_pos := by decide
  sched_len := by decide +kernel
  w1Steps_le := by decide
  mf238_pos := by
    unfold FWBandConfig.mf238 FWBandConfig.m0 FWBandConfig.qbar fwBandBConfig
    norm_num
  w1_eps_nonneg := by
    unfold FWBandConfig.w1Eta fwBandBConfig
    norm_num
  w1_quota := by
    unfold FWBandConfig.w1Eta FWBandConfig.mfW1 FWBandConfig.m0 FWBandConfig.qbar fwBandBConfig
    norm_num
  w1_prefix := by
    have hdec : ∀ j : Fin fwBandBConfig.schedule.length,
        fwBandBConfig.schedule[j.val]? = some .w1 → j.val < fwBandBConfig.w1Steps := by
      decide +kernel
    intro j hj hs
    exact hdec ⟨j, hj⟩ hs
  wheel_rate_le := by
    intro j hj hsub
    have hmu : (34433 / 1018000 : ℝ) ≤ fwBandBConfig.mu j := by
      unfold FWBandConfig.mu FWBandConfig.m0 FWBandConfig.qbar fwBandBConfig
      have hjR : (j : ℝ) ≤ 238 := by exact_mod_cast hj
      norm_num
      linarith
    have hdiv : (6 * fwBandBConfig.qbar) / fwBandBConfig.mu j ≤
        (6 * fwBandBConfig.qbar) / (34433 / 1018000) := by
      unfold FWBandConfig.qbar fwBandBConfig
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmu
    rw [Nat.cast_sub hsub]
    unfold FWBandConfig.mu FWBandConfig.m0 FWBandConfig.qbar fwBandBConfig at hdiv ⊢
    push_cast
    norm_num at hdiv ⊢
    linarith
  bt_prod_eq := by
    unfold FWBandConfig.btEta FWBandConfig.mf238 FWBandConfig.m0 FWBandConfig.qbar fwBandBConfig
    norm_num
  bt_eps_nonneg := by
    unfold FWBandConfig.btEta fwBandBConfig
    norm_num
  bt_quota := by
    dsimp [FWBandConfig.qbar, FWBandConfig.btEta, FWBandConfig.mf238, FWBandConfig.m0, fwBandBConfig]
    norm_num
  gates_ok := fwBandB_gates_ok

theorem fwBandB_envelopes
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 27555 ≤ n) (hnhi : n ≤ 35733) :
    (poolMaximum n : ℝ) ≤ (23601 / 1000 : ℝ) * (n : ℝ) ^ 2 ∧
    fwBandBConfig.m0 * (poolMaximum n : ℝ) ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n ∧
    ((6 * (n + 8) : ℕ) : ℝ) ≤ fwBandBConfig.qbar * (poolMaximum n : ℝ) := by
  have hnloR : (27555 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hnhiR : (n : ℝ) ≤ 35733 := by exact_mod_cast hnhi
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjone : 1 < j := by dsimp [j]; push_cast; nlinarith
  have hjhi : j ≤ 1276847290 := by dsimp [j]; push_cast; nlinarith
  have hlogj : Real.log j < 21 := by
    have h1 := Real.log_le_log hjpos hjhi
    have h2 := log_lt_of_pow_lt_exp 1276847290 21 1 (by norm_num) (by decide) (by norm_num)
    norm_num at h2
    linarith
  have hlog21 : Real.log (21 : ℝ) < 31 / 10 :=
    log_lt_of_pow_lt_exp 21 31 10 (by norm_num) (by decide) (by norm_num)
  have hloglogj : Real.log (Real.log j) < 31 / 10 :=
    lt_of_le_of_lt (Real.log_le_log (Real.log_pos hjone) hlogj.le) hlog21
  have hfactor : Real.log j + Real.log (Real.log j) - 1 / 2 < 118 / 5 := by linarith
  have hu := poolMaximum_upper_sharp upperSharp n (by nlinarith)
  change (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j) - 1 / 2) at hu
  have hprod := mul_lt_mul_of_pos_left hfactor hjpos
  have hXup : (poolMaximum n : ℝ) ≤ (23601 / 1000 : ℝ) * (n : ℝ) ^ 2 := by
    dsimp [j] at hu hprod
    push_cast at hu hprod
    nlinarith
  have hearly : (fwEarlyBudget n : ℝ) ≤ (90 / 1000 : ℝ) * (n : ℝ) ^ 2 := by
    have hdiv : ((n / 450 : ℕ) : ℝ) * 450 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 450
    dsimp [fwEarlyBudget]
    push_cast
    have h1 : (n : ℝ) + 8 ≤ (3445 / 3444 : ℝ) * n := by linarith
    have h2 : 21 + 3 * ((n / 450 : ℕ) : ℝ) ≤ (447 / 60000 : ℝ) * n := by linarith
    have hp := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith
  have hbase : fwBandBConfig.m0 * (poolMaximum n : ℝ) ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n := by
    unfold FWBandConfig.m0 fwBandBConfig
    have hsq : (100000 : ℝ) * 13 ≤ (n : ℝ) ^ 2 := by nlinarith
    push_cast
    nlinarith
  have hjlo : (759278026 : ℝ) ≤ j := by dsimp [j]; push_cast; nlinarith
  have hlogj_lo : (20 : ℝ) < Real.log j := by
    have h1 := lt_log_of_exp_lt_pow 759278026 20 1 (by norm_num) (by decide) (by norm_num)
    norm_num at h1
    have h2 := Real.log_le_log (by norm_num) hjlo
    linarith
  have hXlo_raw := poolMaximum_lower lower n
  change j * Real.log j < (poolMaximum n : ℝ) at hXlo_raw
  have hXlo : (15185560520 : ℝ) < poolMaximum n := by nlinarith
  have hlogX : (117 / 5 : ℝ) < Real.log (poolMaximum n : ℝ) := by
    have h1 : (117 : ℝ) / 5 < Real.log (15185560520 : ℝ) :=
      lt_log_of_exp_lt_pow 15185560520 117 5 (by norm_num) (by decide) (by norm_num)
    have h2 := Real.log_le_log (by norm_num) hXlo.le
    linarith
  have hratio := fw_actual_index_ratio_of_theta (n := n) bmor lower upper (by omega) hnhi
  have hXfw3 : (891 / 40 : ℝ) * (n : ℝ) ^ 2 < poolMaximum n := by
    have hsq : 0 < (n : ℝ) ^ 2 := by positivity
    exact (lt_div_iff₀ hsq).mp (by linarith)
  have hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ fwBandBConfig.qbar * (poolMaximum n : ℝ) := by
    unfold FWBandConfig.qbar fwBandBConfig
    push_cast
    nlinarith
  exact ⟨hXup, hbase, hQ⟩

/-- Unified 238-stage crossing theorem for `21249 ≤ n ≤ 35733`. -/
theorem fw_upper_bands_crossing_of_theta_radius_upper
    (mv : MVBrunTitchmarsh)
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 21249 ≤ n) (hnhi : n ≤ 35733)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages ∧
      stages.length ≤ 238 ∧
      final ⊆ initial ∧
      final.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      (poolMaximum n : ℝ) / 23 ≤ last ∧
      (last : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
  by_cases hA : n ≤ 27554
  · obtain ⟨hXup, hbase, hQ⟩ := fwBandA_envelopes bmor lower upper upperSharp hnlo hA
    have hcrossDet : (poolMaximum n : ℝ) / 23 ≤
        fwBandAConfig.detRadiusAux fwBandAConfig.schedule 0 32 := by
      have hnhiR : (n : ℝ) ≤ 27554 := by exact_mod_cast hA
      have hsq : (n : ℝ) ^ 2 ≤ 27554 ^ 2 := pow_le_pow_left₀ (by positivity) hnhiR 2
      have hdet : (844611524 : ℝ) ≤ fwBandAConfig.detRadiusAux fwBandAConfig.schedule 0 32 := by
        exact_mod_cast fwBandA_det_final
      linarith
    exact fw_band_crossing_of_config mv fwBandAConfig fwBandAConfig_valid hnlo hbase hQ hcrossDet
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
  · have hBlo : 27555 ≤ n := by omega
    obtain ⟨hXup, hbase, hQ⟩ := fwBandB_envelopes bmor lower upper upperSharp hBlo hnhi
    have hcrossDet : (poolMaximum n : ℝ) / 23 ≤
        fwBandBConfig.detRadiusAux fwBandBConfig.schedule 0 32 := by
      have hnhiR : (n : ℝ) ≤ 35733 := by exact_mod_cast hnhi
      have hsq : (n : ℝ) ^ 2 ≤ 35733 ^ 2 := pow_le_pow_left₀ (by positivity) hnhiR 2
      have hdet : (1627156628 : ℝ) ≤ fwBandBConfig.detRadiusAux fwBandBConfig.schedule 0 32 := by
        exact_mod_cast fwBandB_det_final
      linarith
    exact fw_band_crossing_of_config mv fwBandBConfig fwBandBConfig_valid hnlo hbase hQ hcrossDet
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks

end
end Sude
