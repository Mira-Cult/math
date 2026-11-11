import Sude.RSPrimeCountImports
import Sude.FWSharpIndex
import Sude.PoolCountMeanBounds

/-!
# Global Prescribed-Pool Mean Bounds (`n ≥ 2001`)

Proves `449 / 1000 < m / X ∧ m / X < 519 / 1000` uniformly for every order `n ≥ 2001`
(with no upper limit on `n`) from `RSPrimeCountImports` and `RSIndexLowerSharp` via
256-slice Abel partial summation (`PoolCountMeanBounds.oddPrimePool_mean_bounds_of_count_envelopes`).
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

private theorem ratio_factor_split (c X a d : ℝ) (ha : a ≠ 0) :
    (c * X) / d = (c * (a / d)) * (X / a) := by
  by_cases hd : d = 0
  · simp [hd]
  · field_simp

private def pTabArr : Array ℕ := #[0, 0, 16, 25, 32, 37, 41, 44, 48, 50, 53, 55, 57, 59, 60, 62, 64, 65, 66, 67, 69, 70, 71, 72, 73, 74, 75, 76, 76, 77, 78, 79, 80, 80, 81, 82, 82, 83, 83, 84, 85, 85, 86, 86, 87, 87, 88, 88, 89, 89, 90, 90, 91, 91, 92, 92, 92, 93, 93, 94, 94, 94, 95, 95, 96, 96, 96, 97, 97, 97, 98, 98, 98, 99, 99, 99, 99, 100, 100, 100, 101, 101, 101, 102, 102, 102, 102, 103, 103, 103, 103, 104, 104, 104, 104, 105, 105, 105, 105, 106, 106, 106, 106, 106, 107, 107, 107, 107, 108, 108, 108, 108, 108, 109, 109, 109, 109, 109, 110, 110, 110, 110, 110, 111, 111, 111, 111, 111, 112, 112, 112, 112, 112, 112, 113, 113, 113, 113, 113, 113, 114, 114, 114, 114, 114, 114, 115, 115, 115, 115, 115, 115, 115, 116, 116, 116, 116, 116, 116, 117, 117, 117, 117, 117, 117, 117, 118, 118, 118, 118, 118, 118, 118, 118, 119, 119, 119, 119, 119, 119, 119, 119, 120, 120, 120, 120, 120, 120, 120, 120, 121, 121, 121, 121, 121, 121, 121, 121, 122, 122, 122, 122, 122, 122, 122, 122, 122, 123, 123, 123, 123, 123, 123, 123, 123, 123, 124, 124, 124, 124, 124, 124, 124, 124, 124, 125, 125, 125, 125, 125, 125, 125, 125, 125, 125, 126, 126, 126, 126, 126, 126, 126, 126, 126, 126, 126, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 128]
private def qTabArr : Array ℕ := #[0, 0, 16, 26, 32, 38, 42, 45, 48, 51, 54, 56, 58, 60, 61, 63, 64, 66, 67, 68, 70, 71, 72, 73, 74, 75, 76, 77, 77, 78, 79, 80, 80, 81, 82, 83, 83, 84, 84, 85, 86, 86, 87, 87, 88, 88, 89, 89, 90, 90, 91, 91, 92, 92, 93, 93, 93, 94, 94, 95, 95, 95, 96, 96, 96, 97, 97, 98, 98, 98, 99, 99, 99, 100, 100, 100, 100, 101, 101, 101, 102, 102, 102, 103, 103, 103, 103, 104, 104, 104, 104, 105, 105, 105, 105, 106, 106, 106, 106, 107, 107, 107, 107, 107, 108, 108, 108, 108, 109, 109, 109, 109, 109, 110, 110, 110, 110, 110, 111, 111, 111, 111, 111, 112, 112, 112, 112, 112, 112, 113, 113, 113, 113, 113, 114, 114, 114, 114, 114, 114, 115, 115, 115, 115, 115, 115, 116, 116, 116, 116, 116, 116, 116, 117, 117, 117, 117, 117, 117, 118, 118, 118, 118, 118, 118, 118, 119, 119, 119, 119, 119, 119, 119, 119, 120, 120, 120, 120, 120, 120, 120, 120, 121, 121, 121, 121, 121, 121, 121, 121, 122, 122, 122, 122, 122, 122, 122, 122, 123, 123, 123, 123, 123, 123, 123, 123, 123, 124, 124, 124, 124, 124, 124, 124, 124, 124, 125, 125, 125, 125, 125, 125, 125, 125, 125, 126, 126, 126, 126, 126, 126, 126, 126, 126, 126, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128]
private def hiCoeffArr : Array ℕ := #[69211, 118063, 171261, 222644, 273426, 323574, 373627, 421237, 470714, 517807, 565831, 613226, 660003, 708467, 754179, 799304, 846550, 893494, 940141, 983384, 1029308, 1074945, 1120297, 1165367, 1210157, 1254670, 1298908, 1347016, 1390834, 1434384, 1477667, 1520687, 1568209, 1610823, 1653179, 1700413, 1742370, 1789461, 1831025, 1872339, 1919148, 1960074, 2006743, 2047286, 2093815, 2133979, 2180370, 2220158, 2266412, 2305828, 2351944, 2390992, 2436973, 2475656, 2521502, 2567347, 2605535, 2651246, 2689077, 2734655, 2780232, 2817578, 2863022, 2900019, 2945331, 2990644, 3027163, 3072345, 3117526, 3153574, 3198625, 3243676, 3279256, 3324178, 3369099, 3414020, 3449009, 3493802, 3538594, 3573126, 3617790, 3662454, 3696534, 3741071, 3785607, 3830144, 3863650, 3908059, 3952469, 3996879, 4029816, 4074100, 4118383, 4162667, 4195042, 4239200, 4283358, 4327516, 4359334, 4403368, 4447402, 4491435, 4535469, 4566612, 4610522, 4654431, 4698341, 4728939, 4772726, 4816512, 4860299, 4904085, 4934022, 4977686, 5021350, 5065014, 5108678, 5137960, 5181502, 5225044, 5268586, 5312128, 5340762, 5384183, 5427604, 5471025, 5514445, 5542439, 5585739, 5629039, 5672339, 5715640, 5758940, 5786179, 5829359, 5872540, 5915720, 5958901, 6002081, 6028574, 6071635, 6114696, 6157757, 6200819, 6243880, 6269634, 6312577, 6355519, 6398462, 6441405, 6484347, 6527290, 6552195, 6595020, 6637845, 6680670, 6723494, 6766319, 6790502, 6833209, 6875917, 6918624, 6961332, 7004040, 7046747, 7070098, 7112689, 7155280, 7197871, 7240462, 7283053, 7325644, 7368235, 7390647, 7433122, 7475597, 7518072, 7560546, 7603021, 7645496, 7687971, 7709454, 7751814, 7794174, 7836533, 7878893, 7921252, 7963612, 8005972, 8026535, 8068780, 8111025, 8153270, 8195515, 8237760, 8280005, 8322250, 8341903, 8384034, 8426165, 8468296, 8510427, 8552557, 8594688, 8636819, 8678950, 8697590, 8739607, 8781625, 8823642, 8865659, 8907677, 8949694, 8991711, 9033729, 9051365, 9093270, 9135174, 9177079, 9218983, 9260888, 9302792, 9344697, 9386601, 9403245, 9445038, 9486830, 9528622, 9570414, 9612206, 9653999, 9695791, 9737583, 9779375, 9794925, 9836606, 9878286, 9919967, 9961647, 10003328, 10045009, 10086689, 10128370, 10170050, 10211731, 10226087, 10267657, 10309226, 10350796, 10392365, 10433935, 10475504, 10517074, 10558643, 10600212, 10613498]
private def loCoeffArr : Array ℕ := #[0, 39061, 78124, 117186, 156249, 195311, 234374, 273436, 312499, 351561, 390624, 429686, 468749, 507811, 546874, 585936, 624999, 664061, 703124, 742186, 781249, 820311, 859374, 898436, 937499, 976561, 1015624, 1054686, 1093749, 1132811, 1171874, 1210936, 1249999, 1289061, 1328124, 1367186, 1406249, 1445311, 1484374, 1523436, 1562499, 1601561, 1640624, 1679686, 1718749, 1757811, 1796874, 1835936, 1874999, 1914061, 1953124, 1992186, 2031249, 2070311, 2109374, 2148436, 2187499, 2226561, 2265624, 2304686, 2343749, 2382811, 2421874, 2460936, 2499999, 2539061, 2578124, 2617186, 2656249, 2695311, 2734374, 2773436, 2812499, 2851561, 2890624, 2929686, 2968749, 3007811, 3046874, 3085936, 3124999, 3164061, 3203124, 3242186, 3281249, 3320311, 3359374, 3398436, 3437499, 3476561, 3515624, 3553901, 3592955, 3632009, 3671063, 3700284, 3739234, 3778185, 3817135, 3845893, 3884741, 3923588, 3962436, 4001283, 4029480, 4068225, 4106970, 4145715, 4173458, 4212101, 4250744, 4289388, 4328031, 4355223, 4393765, 4432306, 4470848, 4509390, 4536037, 4574478, 4612919, 4651360, 4689801, 4715907, 4754248, 4792589, 4830930, 4869270, 4907611, 4933083, 4971324, 5009565, 5047806, 5086047, 5110990, 5149131, 5187273, 5225415, 5263557, 5301698, 5326018, 5364061, 5402104, 5440147, 5478190, 5516233, 5539937, 5577882, 5615826, 5653771, 5691716, 5729661, 5767605, 5790601, 5828448, 5866295, 5904142, 5941989, 5979836, 6002227, 6039977, 6077726, 6115476, 6153226, 6190976, 6228726, 6250422, 6288075, 6325728, 6363381, 6401034, 6438688, 6476341, 6513994, 6534905, 6572462, 6610019, 6647576, 6685133, 6722690, 6760247, 6797804, 6817939, 6855400, 6892861, 6930322, 6967784, 7005245, 7042706, 7080167, 7099533, 7136899, 7174265, 7211631, 7248997, 7286363, 7323729, 7361095, 7379699, 7416970, 7454241, 7491513, 7528784, 7566055, 7603326, 7640597, 7677869, 7695625, 7732802, 7769978, 7807155, 7844332, 7881509, 7918686, 7955863, 7993040, 8009956, 8047039, 8084122, 8121205, 8158289, 8195372, 8232455, 8269538, 8306621, 8322705, 8359695, 8396685, 8433675, 8470664, 8507654, 8544644, 8581634, 8618624, 8655613, 8670781, 8707678, 8744575, 8781472, 8818369, 8855266, 8892163, 8929060, 8965957, 9002854, 9039751, 9053918, 9090723, 9127527, 9164332, 9201137, 9237941, 9274746, 9311550, 9348355, 9385159]

private def pTab (s : ℕ) : ℕ := pTabArr.getD s 0
private def qTab (s : ℕ) : ℕ := qTabArr.getD s 0
private def hiCoeff (s : ℕ) : ℕ := hiCoeffArr.getD s 0
private def loCoeff (s : ℕ) : ℕ := loCoeffArr.getD s 0

private theorem pTab_one : pTab 1 = 0 := by decide +kernel
private theorem loCoeff_zero : loCoeff 0 = 0 := by decide +kernel

private theorem pq_pow_bounds :
    ∀ s ∈ Finset.Icc 1 256,
      pTab s ≤ 128 ∧ qTab s ≤ 128 ∧
      2 ^ (pTab s) ≤ s ^ 16 ∧ s ^ 16 ≤ 2 ^ (qTab s) := by
  decide +kernel

private theorem hiCoeff_zero_check :
    62753 * 173 * 1000000000 * 10000000 ≤
      hiCoeff 0 * (50000 * 256 * (178 * 1000000000 - 8 * 6931471808)) := by
  decide +kernel

private theorem hiCoeff_pos_check :
    ∀ s ∈ Finset.Icc 1 255,
      (128 - pTab (s + 1)) * 6931471808 < 163 * 16 * 1000000000 ∧
      (s + 1) * 173 * 16 * 1000000000 * 10000000 ≤
        hiCoeff s * (256 * (163 * 16 * 1000000000 - (128 - pTab (s + 1)) * 6931471808)) := by
  decide +kernel

private theorem loCoeff_pos_check :
    ∀ s ∈ Finset.Icc 1 255,
      (128 - qTab s) * 6931471803 < 173 * 16 * 1000000000 ∧
      (if (128 - qTab s) * 6931471803 ≤ 16 * 10000000000 then
        loCoeff s * (256 * (173 * 16 * 1000000000 - (128 - qTab s) * 6931471803)) ≤
          s * 163 * 16 * 1000000000 * 10000000
      else
        loCoeff s * 256 ≤ s * 10000000) := by
  decide +kernel

private theorem sum_hiCoeff_eq :
    (∑ s ∈ Finset.range 256, hiCoeff s) = 1410268367 := by
  decide +kernel

private theorem sum_loCoeff_eq :
    (∑ s ∈ Finset.range 256, loCoeff s) = 1231373994 := by
  decide +kernel

private theorem log_two_bounds_d9 :
    (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧
    Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
  constructor
  · have h := Real.log_two_gt_d9
    norm_num at h ⊢
    exact h
  · have h := Real.log_two_lt_d9
    norm_num at h ⊢
    exact h

private theorem exp_three_halves_lt_nine : Real.exp (3 / 2 : ℝ) < 9 := by
  have he1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have he1_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : Real.exp 2 < 9 := by
    have hadd : Real.exp ((1 : ℝ) + 1) = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
    norm_num at hadd
    rw [hadd]
    nlinarith
  have he3 : Real.exp (3 / 2 : ℝ) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  linarith

/-- For `n ≥ 2001`, `poolMaximum n > 65170000` and `178 / 10 < Real.log (poolMaximum n)`. -/
theorem poolMaximum_gt_65170000_and_log_gt
    (sharp : RSIndexLowerSharp) {n : ℕ} (hn : 2001 ≤ n) :
    65170000 < poolMaximum n ∧ (178 / 10 : ℝ) < Real.log (poolMaximum n : ℝ) := by
  have hnreal : (2001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (4004002 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hjpos : 0 < j := by linarith
  have hjpow : (2 : ℝ) ^ 219 < j ^ 10 := by
    have h1 : (2 : ℝ) ^ 219 < (4004002 : ℝ) ^ 10 := by norm_num
    have h2 : (4004002 : ℝ) ^ 10 ≤ j ^ 10 := pow_le_pow_left₀ (by norm_num) hj 10
    exact lt_of_lt_of_le h1 h2
  have hlogj : (15179 / 1000 : ℝ) < Real.log j := by
    have h := Real.log_lt_log (by positivity) hjpow
    rw [Real.log_pow, Real.log_pow] at h
    have hln2 := log_two_bounds_d9.1
    push_cast at h
    linarith
  have hllpow : (2 : ℝ) ^ 15 < (Real.log j) ^ 4 := by
    have h1 : (2 : ℝ) ^ 15 < (15179 / 1000 : ℝ) ^ 4 := by norm_num
    have h2 : (15179 / 1000 : ℝ) ^ 4 ≤ (Real.log j) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hlogj.le 4
    exact lt_of_lt_of_le h1 h2
  have hloglogj : (2599 / 1000 : ℝ) < Real.log (Real.log j) := by
    have h := Real.log_lt_log (by positivity) hllpow
    rw [Real.log_pow, Real.log_pow] at h
    have hln2 := log_two_bounds_d9.1
    push_cast at h
    linarith
  have hsource : j * (Real.log j + Real.log (Real.log j) - 3 / 2) < (poolMaximum n : ℝ) := by
    have hn2 : 1 ≤ n * n := Nat.mul_pos (by omega) (by omega)
    simpa [j, poolMaximum] using sharp (n * n + 1) (by omega)
  have hXreal : (65170000 : ℝ) < (poolMaximum n : ℝ) := by
    have hfac : (16278 / 1000 : ℝ) < Real.log j + Real.log (Real.log j) - 3 / 2 := by linarith
    have hmul : j * (16278 / 1000 : ℝ) < j * (Real.log j + Real.log (Real.log j) - 3 / 2) :=
      mul_lt_mul_of_pos_left hfac hjpos
    linarith
  have hXnat : 65170000 < poolMaximum n := by exact_mod_cast hXreal
  refine ⟨hXnat, ?_⟩
  have hXpow : (2 : ℝ) ^ 103 < (poolMaximum n : ℝ) ^ 4 := by
    have h1 : (2 : ℝ) ^ 103 < (65170000 : ℝ) ^ 4 := by norm_num
    have h2 : (65170000 : ℝ) ^ 4 ≤ (poolMaximum n : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hXreal.le 4
    exact lt_of_lt_of_le h1 h2
  have h := Real.log_lt_log (by positivity) hXpow
  rw [Real.log_pow, Real.log_pow] at h
  have hln2 := log_two_bounds_d9.1
  push_cast at h
  linarith

private theorem log_slice_bounds {X s : ℕ} (hX : 0 < X) (hs : 1 ≤ s) (hs256 : s ≤ 256) :
    Real.log (X : ℝ) - ((128 - pTab s : ℕ) : ℝ) / 16 * (6931471808 / 10000000000 : ℝ) ≤
      Real.log ((s : ℝ) * (X : ℝ) / 256) ∧
    Real.log ((s : ℝ) * (X : ℝ) / 256) ≤
      Real.log (X : ℝ) - ((128 - qTab s : ℕ) : ℝ) / 16 * (6931471803 / 10000000000 : ℝ) := by
  have hpq := pq_pow_bounds s (Finset.mem_Icc.mpr ⟨hs, hs256⟩)
  obtain ⟨hp128, hq128, hplo, hqhi⟩ := hpq
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hploR : (2 : ℝ) ^ (pTab s) ≤ (s : ℝ) ^ 16 := by exact_mod_cast hplo
  have hqhiR : (s : ℝ) ^ 16 ≤ (2 : ℝ) ^ (qTab s) := by exact_mod_cast hqhi
  have hlogs_lo : ((pTab s : ℝ) / 16) * Real.log 2 ≤ Real.log (s : ℝ) := by
    have h := Real.log_le_log (by positivity) hploR
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hlogs_hi : Real.log (s : ℝ) ≤ ((qTab s : ℝ) / 16) * Real.log 2 := by
    have h := Real.log_le_log (by positivity) hqhiR
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hsplit : Real.log ((s : ℝ) * (X : ℝ) / 256) =
      Real.log (X : ℝ) + Real.log (s : ℝ) - 8 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num),
        Real.log_mul (ne_of_gt hspos) (ne_of_gt hXpos),
        show (256 : ℝ) = (2 : ℝ) ^ 8 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [hsplit]
  have hln2 := log_two_bounds_d9
  have hsub_p : ((128 - pTab s : ℕ) : ℝ) = 128 - (pTab s : ℝ) := Nat.cast_sub hp128
  have hsub_q : ((128 - qTab s : ℕ) : ℝ) = 128 - (qTab s : ℝ) := Nat.cast_sub hq128
  rw [hsub_p, hsub_q]
  have hp_nonneg : (0 : ℝ) ≤ (128 - (pTab s : ℝ)) / 16 := by
    have : (pTab s : ℝ) ≤ 128 := by exact_mod_cast hp128
    linarith
  have hq_nonneg : (0 : ℝ) ≤ (128 - (qTab s : ℝ)) / 16 := by
    have : (qTab s : ℝ) ≤ 128 := by exact_mod_cast hq128
    linarith
  have hp_mul : ((pTab s : ℝ) / 16 - 8) * Real.log 2 ≥
      -((128 - (pTab s : ℝ)) / 16) * (6931471808 / 10000000000 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hln2.2.le hp_nonneg
    linarith
  have hq_mul : ((qTab s : ℝ) / 16 - 8) * Real.log 2 ≤
      -((128 - (qTab s : ℝ)) / 16) * (6931471803 / 10000000000 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hln2.1.le hq_nonneg
    linarith
  constructor <;> linarith

private theorem fiber_eq_Ico {X s : ℕ} (hX : 0 < X) (hs : s < 256) :
    (Finset.range X).filter (fun k => (256 * k) / X = s) =
      Finset.Ico ((s * X + 255) / 256) (((s + 1) * X + 255) / 256) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨_hkX, hdiv⟩
    have h1 : s * X ≤ 256 * k := by
      rw [← hdiv]
      exact Nat.div_mul_le_self (256 * k) X
    have h2 : 256 * k < (s + 1) * X := by
      rw [← hdiv, Nat.add_mul, one_mul]
      have hdm := Nat.div_add_mod (256 * k) X
      have hlt := Nat.mod_lt (256 * k) hX
      have hcomm : (256 * k / X) * X = X * (256 * k / X) := Nat.mul_comm _ _
      omega
    omega
  · rintro ⟨hlo, hhi⟩
    have h1 : s * X ≤ 256 * k := by omega
    have h2 : 256 * k < (s + 1) * X := by omega
    have hkX : k < X := by
      have hlt256 : (s + 1) * X ≤ 256 * X := Nat.mul_le_mul_right X (by omega)
      omega
    refine ⟨hkX, ?_⟩
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hX).mpr h2)
    · exact (Nat.le_div_iff_mul_le hX).mpr h1

private theorem fiber_card_bounds {X s : ℕ} (hX : 0 < X) (hs : s < 256) :
    X / 256 ≤ ((Finset.range X).filter (fun k => (256 * k) / X = s)).card ∧
    ((Finset.range X).filter (fun k => (256 * k) / X = s)).card ≤ X / 256 + 1 := by
  rw [fiber_eq_Ico hX hs, Nat.card_Ico, Nat.add_mul, one_mul]
  omega

private theorem range_biUnion_fibers {X : ℕ} (hX : 0 < X) :
    (Finset.range 256).biUnion (fun s => (Finset.range X).filter (fun k => (256 * k) / X = s)) =
      Finset.range X := by
  ext k
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
  constructor
  · rintro ⟨_s, _hs, hk, _⟩
    exact hk
  · intro hk
    exact ⟨(256 * k) / X, (Nat.div_lt_iff_lt_mul hX).mpr (by omega), hk, rfl⟩

private def hiSliceVal (X : ℕ) (s : ℕ) : ℝ :=
  (hiCoeff s : ℝ) / 10000000 * ((X : ℝ) / (Real.log (X : ℝ) - 1 / 2))

private def loSliceVal (X : ℕ) (s : ℕ) : ℝ :=
  if s = 0 then 0 else (loCoeff s : ℝ) / 10000000 * ((X : ℝ) / (Real.log (X : ℝ) - 3 / 2)) - 1

private theorem hi_envelope_le
    (rs : RSPrimeCountImports) {X : ℕ}
    (hX : 65170000 < X) (hu : (178 / 10 : ℝ) < Real.log (X : ℝ))
    {k : ℕ} (hk : k < X) :
    ((oddPrimePrefix k).card : ℝ) ≤ hiSliceVal X ((256 * k) / X) := by
  have hXpos : 0 < X := by omega
  have hXR_gt : (65170000 : ℝ) < (X : ℝ) := Nat.cast_lt.mpr hX
  have hXR_pos : 0 < (X : ℝ) := by linarith
  have hu_half_pos : 0 < Real.log (X : ℝ) - 1 / 2 := by linarith
  let s := (256 * k) / X
  change ((oddPrimePrefix k).card : ℝ) ≤ hiSliceVal X s
  have hs_lt : s < 256 := (Nat.div_lt_iff_lt_mul hXpos).mpr (by omega)
  have hk_hi_nat : 256 * k < (s + 1) * X := by
    dsimp [s]
    rw [Nat.add_mul, one_mul]
    have hdm := Nat.div_add_mod (256 * k) X
    have hlt := Nat.mod_lt (256 * k) hXpos
    have hcomm : (256 * k / X) * X = X * (256 * k / X) := Nat.mul_comm _ _
    omega
  have hk_le_ys : (k : ℝ) ≤ ((s + 1 : ℕ) : ℝ) * (X : ℝ) / 256 := by
    have hcast : ((256 * k : ℕ) : ℝ) ≤ (((s + 1) * X : ℕ) : ℝ) := Nat.cast_le.mpr hk_hi_nat.le
    push_cast at hcast ⊢
    linarith
  have hstep1 : ((oddPrimePrefix k).card : ℝ) ≤
      primeCountReal (((s + 1 : ℕ) : ℝ) * (X : ℝ) / 256) :=
    (oddPrimePrefix_card_le_primeCountReal k).trans (primeCountReal_mono hk_le_ys)
  by_cases hs0 : s = 0
  · rw [hs0] at hstep1 ⊢
    dsimp [hiSliceVal]
    simp only [Nat.zero_add, Nat.cast_one, one_mul] at hstep1
    have hy0_gt : 1 < (X : ℝ) / 256 := by linarith
    have hpi0 := (rs.upper ((X : ℝ) / 256) hy0_gt).le
    have hlog_y0 : Real.log (X : ℝ) - 8 * (6931471808 / 10000000000 : ℝ) ≤
        Real.log ((X : ℝ) / 256) := by
      have h := (log_slice_bounds hXpos (s := 1) (by omega) (by omega)).1
      rw [pTab_one] at h
      norm_num at h ⊢
      exact h
    have hden0_pos : 0 < Real.log (X : ℝ) - 8 * (6931471808 / 10000000000 : ℝ) := by linarith
    have hmono_u : (Real.log (X : ℝ) - 1 / 2) /
        (Real.log (X : ℝ) - 8 * (6931471808 / 10000000000 : ℝ)) ≤
        (178 / 10 - 1 / 2 : ℝ) / (178 / 10 - 8 * (6931471808 / 10000000000 : ℝ)) := by
      rw [div_le_div_iff₀ hden0_pos (by norm_num)]
      linarith
    have hc0 : (62753 / 50000 : ℝ) * (1 / 256) *
        ((178 / 10 - 1 / 2 : ℝ) / (178 / 10 - 8 * (6931471808 / 10000000000 : ℝ))) ≤
        (hiCoeff 0 : ℝ) / 10000000 := by
      have hchk : ((62753 * 173 * 1000000000 * 10000000 : ℕ) : ℝ) ≤
          ((hiCoeff 0 * (50000 * 256 * (178 * 1000000000 - 8 * 6931471808)) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hiCoeff_zero_check
      push_cast at hchk
      linarith
    have hbound_coeff : (62753 / 50000 : ℝ) * (1 / 256) *
        ((Real.log (X : ℝ) - 1 / 2) /
          (Real.log (X : ℝ) - 8 * (6931471808 / 10000000000 : ℝ))) ≤
        (hiCoeff 0 : ℝ) / 10000000 := by
      have hm := mul_le_mul_of_nonneg_left hmono_u
        (show (0 : ℝ) ≤ (62753 / 50000 : ℝ) * (1 / 256) by norm_num)
      exact hm.trans hc0
    have hdiv_log : (62753 / 50000 : ℝ) * ((X : ℝ) / 256) / Real.log ((X : ℝ) / 256) ≤
        (62753 / 50000 : ℝ) * ((X : ℝ) / 256) /
          (Real.log (X : ℝ) - 8 * (6931471808 / 10000000000 : ℝ)) :=
      div_le_div_of_nonneg_left (by linarith) hden0_pos hlog_y0
    have halg : (62753 / 50000 : ℝ) * ((X : ℝ) / 256) /
        (Real.log (X : ℝ) - 8 * (6931471808 / 10000000000 : ℝ)) =
        ((62753 / 50000 : ℝ) * (1 / 256) *
          ((Real.log (X : ℝ) - 1 / 2) /
            (Real.log (X : ℝ) - 8 * (6931471808 / 10000000000 : ℝ)))) *
          ((X : ℝ) / (Real.log (X : ℝ) - 1 / 2)) := by
      have h1 : (62753 / 50000 : ℝ) * ((X : ℝ) / 256) =
          ((62753 / 50000 : ℝ) * (1 / 256)) * (X : ℝ) := by ring
      rw [h1]
      exact ratio_factor_split _ _ _ _ hu_half_pos.ne'
    have hmul := mul_le_mul_of_nonneg_right hbound_coeff
      (div_nonneg hXR_pos.le hu_half_pos.le)
    linarith
  · have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hs0
    have hs_mem : s ∈ Finset.Icc 1 255 := Finset.mem_Icc.mpr ⟨hs1, by omega⟩
    obtain ⟨hden_nat, hcoeff_nat⟩ := hiCoeff_pos_check s hs_mem
    let ys : ℝ := ((s + 1 : ℕ) : ℝ) * (X : ℝ) / 256
    have hys_pos : 0 < ys := by
      dsimp [ys]
      exact div_pos (mul_pos (Nat.cast_pos.mpr (by omega)) hXR_pos) (by norm_num)
    have hys_gt : Real.exp (3 / 2 : ℝ) < ys := by
      have h1 : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := Nat.one_le_cast.mpr (by omega)
      have h2 : (X : ℝ) ≤ ((s + 1 : ℕ) : ℝ) * (X : ℝ) := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right h1 hXR_pos.le
      have h3 : (X : ℝ) / 256 ≤ ys := by
        dsimp [ys]
        linarith
      linarith [exp_three_halves_lt_nine]
    have hpi_s := (rs.upper_sharp ys hys_gt).le
    let cs : ℝ := ((128 - pTab (s + 1) : ℕ) : ℝ) / 16 * (6931471808 / 10000000000 : ℝ)
    have hlog_ys : Real.log (X : ℝ) - cs ≤ Real.log ys :=
      (log_slice_bounds hXpos (s := s + 1) (by omega) (by omega)).1
    have hcs_nonneg : 0 ≤ cs := by
      dsimp [cs]
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (by norm_num)
    have hden0_pos : 0 < (178 / 10 : ℝ) - 3 / 2 - cs := by
      have hchk : (((128 - pTab (s + 1)) * 6931471808 : ℕ) : ℝ) <
          ((163 * 16 * 1000000000 : ℕ) : ℝ) := Nat.cast_lt.mpr hden_nat
      dsimp [cs]
      push_cast at hchk
      linarith
    have hden_u_pos : 0 < Real.log (X : ℝ) - 3 / 2 - cs := by linarith
    have hmono_u : (Real.log (X : ℝ) - 1 / 2) / (Real.log (X : ℝ) - 3 / 2 - cs) ≤
        ((178 / 10 : ℝ) - 1 / 2) / ((178 / 10 : ℝ) - 3 / 2 - cs) := by
      rw [div_le_div_iff₀ hden_u_pos hden0_pos]
      have hid : ((178 / 10 : ℝ) - 1 / 2) * (Real.log (X : ℝ) - 3 / 2 - cs) -
          (Real.log (X : ℝ) - 1 / 2) * ((178 / 10 : ℝ) - 3 / 2 - cs) =
          (Real.log (X : ℝ) - 178 / 10) * (1 + cs) := by ring
      have hprod : 0 ≤ (Real.log (X : ℝ) - 178 / 10) * (1 + cs) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    have hcoeff : (((s + 1 : ℕ) : ℝ) / 256) *
        (((178 / 10 : ℝ) - 1 / 2) / ((178 / 10 : ℝ) - 3 / 2 - cs)) ≤
        (hiCoeff s : ℝ) / 10000000 := by
      rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos (by norm_num) hden0_pos) (by norm_num)]
      have hchk : (((s + 1) * 173 * 16 * 1000000000 * 10000000 : ℕ) : ℝ) ≤
          ((hiCoeff s * (256 * (163 * 16 * 1000000000 - (128 - pTab (s + 1)) * 6931471808)) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcoeff_nat
      push_cast [Nat.cast_sub hden_nat.le] at hchk
      dsimp [cs]
      push_cast
      linarith
    have hdiv_log : ys / (Real.log ys - 3 / 2) ≤ ys / (Real.log (X : ℝ) - 3 / 2 - cs) :=
      div_le_div_of_nonneg_left hys_pos.le hden_u_pos (by linarith)
    have halg : ys / (Real.log (X : ℝ) - 3 / 2 - cs) =
        ((((s + 1 : ℕ) : ℝ) / 256) *
          ((Real.log (X : ℝ) - 1 / 2) / (Real.log (X : ℝ) - 3 / 2 - cs))) *
          ((X : ℝ) / (Real.log (X : ℝ) - 1 / 2)) := by
      have h1 : ys = (((s + 1 : ℕ) : ℝ) / 256) * (X : ℝ) := by dsimp [ys]; ring
      rw [h1]
      exact ratio_factor_split _ _ _ _ hu_half_pos.ne'
    have hbound_u : (((s + 1 : ℕ) : ℝ) / 256) *
        ((Real.log (X : ℝ) - 1 / 2) / (Real.log (X : ℝ) - 3 / 2 - cs)) ≤
        (hiCoeff s : ℝ) / 10000000 := by
      have hm := mul_le_mul_of_nonneg_left hmono_u
        (show (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) / 256 by positivity)
      exact hm.trans hcoeff
    have hmul := mul_le_mul_of_nonneg_right hbound_u
      (div_nonneg hXR_pos.le hu_half_pos.le)
    dsimp [hiSliceVal]
    change ((oddPrimePrefix k).card : ℝ) ≤
      (hiCoeff s : ℝ) / 10000000 * ((X : ℝ) / (Real.log (X : ℝ) - 1 / 2))
    linarith

private theorem lo_envelope_ge
    (rs : RSPrimeCountImports) {X : ℕ}
    (hX : 65170000 < X) (hu : (178 / 10 : ℝ) < Real.log (X : ℝ))
    {k : ℕ} (hk : k < X) :
    loSliceVal X ((256 * k) / X) ≤ ((oddPrimePrefix k).card : ℝ) := by
  have hXpos : 0 < X := by omega
  have hXR_gt : (65170000 : ℝ) < (X : ℝ) := Nat.cast_lt.mpr hX
  have hXR_pos : 0 < (X : ℝ) := by linarith
  have hu_three_pos : 0 < Real.log (X : ℝ) - 3 / 2 := by linarith
  let s := (256 * k) / X
  change loSliceVal X s ≤ ((oddPrimePrefix k).card : ℝ)
  have hs_lt : s < 256 := (Nat.div_lt_iff_lt_mul hXpos).mpr (by omega)
  dsimp [loSliceVal]
  by_cases hs0 : s = 0
  · rw [if_pos hs0]
    exact Nat.cast_nonneg _
  · rw [if_neg hs0]
    have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hs0
    have hk_lo_nat : s * X ≤ 256 * k := Nat.div_mul_le_self (256 * k) X
    have hk_ge_2 : 2 ≤ k := by
      have h1 : 1 * X ≤ s * X := Nat.mul_le_mul_right X hs1
      omega
    have hodd_eq : ((oddPrimePrefix k).card : ℝ) = primeCountReal (k : ℝ) - 1 := by
      linarith [primeCountReal_natCast_eq_oddPrefix_add_one hk_ge_2]
    rw [hodd_eq]
    let xs : ℝ := (s : ℝ) * (X : ℝ) / 256
    have hxs_le_k : xs ≤ (k : ℝ) := by
      dsimp [xs]
      have hcast : ((s * X : ℕ) : ℝ) ≤ ((256 * k : ℕ) : ℝ) := Nat.cast_le.mpr hk_lo_nat
      push_cast at hcast
      linarith
    have hxs_ge_67 : 67 ≤ xs := by
      have h1 : (1 : ℝ) ≤ (s : ℝ) := Nat.one_le_cast.mpr hs1
      have h2 : (X : ℝ) ≤ (s : ℝ) * (X : ℝ) := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right h1 hXR_pos.le
      dsimp [xs]
      linarith
    have hpi_lo : xs / (Real.log xs - 1 / 2) ≤ primeCountReal (k : ℝ) :=
      (rs.lower_sharp xs hxs_ge_67).le.trans (primeCountReal_mono hxs_le_k)
    let ds : ℝ := ((128 - qTab s : ℕ) : ℝ) / 16 * (6931471803 / 10000000000 : ℝ)
    have hlog_xs : Real.log xs ≤ Real.log (X : ℝ) - ds :=
      (log_slice_bounds hXpos hs1 (by omega)).2
    have hs_mem : s ∈ Finset.Icc 1 255 := Finset.mem_Icc.mpr ⟨hs1, by omega⟩
    obtain ⟨hden_nat, hcoeff_nat⟩ := loCoeff_pos_check s hs_mem
    have hden0_pos : 0 < (178 / 10 : ℝ) - 1 / 2 - ds := by
      have hchk : (((128 - qTab s) * 6931471803 : ℕ) : ℝ) <
          ((173 * 16 * 1000000000 : ℕ) : ℝ) := Nat.cast_lt.mpr hden_nat
      dsimp [ds]
      push_cast at hchk
      linarith
    have hden_u_pos : 0 < Real.log (X : ℝ) - 1 / 2 - ds := by linarith
    have hlog_pos : 0 < Real.log xs - 1 / 2 := by
      have h2 : Real.log 2 < Real.log xs := Real.log_lt_log (by norm_num) (by linarith)
      linarith [log_two_bounds_d9.1]
    have hdiv_log : xs / (Real.log (X : ℝ) - 1 / 2 - ds) ≤ xs / (Real.log xs - 1 / 2) :=
      div_le_div_of_nonneg_left (by linarith) hlog_pos (by linarith)
    have halg : xs / (Real.log (X : ℝ) - 1 / 2 - ds) =
        (((s : ℝ) / 256) * ((Real.log (X : ℝ) - 3 / 2) / (Real.log (X : ℝ) - 1 / 2 - ds))) *
          ((X : ℝ) / (Real.log (X : ℝ) - 3 / 2)) := by
      have h1 : xs = ((s : ℝ) / 256) * (X : ℝ) := by dsimp [xs]; ring
      rw [h1]
      exact ratio_factor_split _ _ _ _ hu_three_pos.ne'
    have hcoeff_u : (loCoeff s : ℝ) / 10000000 ≤
        ((s : ℝ) / 256) * ((Real.log (X : ℝ) - 3 / 2) / (Real.log (X : ℝ) - 1 / 2 - ds)) := by
      by_cases hds_nat : (128 - qTab s) * 6931471803 ≤ 16 * 10000000000
      · rw [if_pos hds_nat] at hcoeff_nat
        have hds_le : ds ≤ 1 := by
          have hchk : (((128 - qTab s) * 6931471803 : ℕ) : ℝ) ≤
              ((16 * 10000000000 : ℕ) : ℝ) := Nat.cast_le.mpr hds_nat
          dsimp [ds]
          push_cast at hchk
          linarith
        have hmono : ((178 / 10 : ℝ) - 3 / 2) / ((178 / 10 : ℝ) - 1 / 2 - ds) ≤
            (Real.log (X : ℝ) - 3 / 2) / (Real.log (X : ℝ) - 1 / 2 - ds) := by
          rw [div_le_div_iff₀ hden0_pos hden_u_pos]
          have hid : (Real.log (X : ℝ) - 3 / 2) * ((178 / 10 : ℝ) - 1 / 2 - ds) -
              ((178 / 10 : ℝ) - 3 / 2) * (Real.log (X : ℝ) - 1 / 2 - ds) =
              (Real.log (X : ℝ) - 178 / 10) * (1 - ds) := by ring
          have hprod : 0 ≤ (Real.log (X : ℝ) - 178 / 10) * (1 - ds) :=
            mul_nonneg (by linarith) (by linarith)
          linarith
        have h0 : (loCoeff s : ℝ) / 10000000 ≤
            ((s : ℝ) / 256) * (((178 / 10 : ℝ) - 3 / 2) / ((178 / 10 : ℝ) - 1 / 2 - ds)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (by norm_num) (mul_pos (by norm_num) hden0_pos)]
          have hchk : ((loCoeff s * (256 * (173 * 16 * 1000000000 - (128 - qTab s) * 6931471803)) : ℕ) : ℝ) ≤
              ((s * 163 * 16 * 1000000000 * 10000000 : ℕ) : ℝ) := Nat.cast_le.mpr hcoeff_nat
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hden_nat.le] at hchk
          dsimp [ds]
          push_cast at hchk ⊢
          linarith
        exact h0.trans (mul_le_mul_of_nonneg_left hmono (div_nonneg (Nat.cast_nonneg _) (by norm_num)))
      · rw [if_neg hds_nat] at hcoeff_nat
        have hds_gt : 1 < ds := by
          have hchk : ((16 * 10000000000 : ℕ) : ℝ) <
              (((128 - qTab s) * 6931471803 : ℕ) : ℝ) := Nat.cast_lt.mpr (lt_of_not_ge hds_nat)
          dsimp [ds]
          push_cast at hchk
          linarith
        have h1 : (1 : ℝ) ≤ (Real.log (X : ℝ) - 3 / 2) / (Real.log (X : ℝ) - 1 / 2 - ds) := by
          rw [one_le_div hden_u_pos]
          linarith
        have h0 : (loCoeff s : ℝ) / 10000000 ≤ (s : ℝ) / 256 := by
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
          have hchk : ((loCoeff s * 256 : ℕ) : ℝ) ≤ ((s * 10000000 : ℕ) : ℝ) :=
            Nat.cast_le.mpr hcoeff_nat
          push_cast at hchk
          linarith
        calc
          (loCoeff s : ℝ) / 10000000 ≤ ((s : ℝ) / 256) * 1 := by linarith
          _ ≤ ((s : ℝ) / 256) * ((Real.log (X : ℝ) - 3 / 2) / (Real.log (X : ℝ) - 1 / 2 - ds)) :=
            mul_le_mul_of_nonneg_left h1 (div_nonneg (Nat.cast_nonneg _) (by norm_num))
    have hmul := mul_le_mul_of_nonneg_right hcoeff_u (div_nonneg hXR_pos.le hu_three_pos.le)
    linarith

private theorem fibers_pairwiseDisjoint {X : ℕ} :
    (Finset.range 256 : Set ℕ).PairwiseDisjoint
      (fun s => (Finset.range X).filter (fun k => (256 * k) / X = s)) := by
  intro s1 _ s2 _ hne
  change Disjoint _ _
  rw [Finset.disjoint_left]
  intro k hk1 hk2
  exact hne ((Finset.mem_filter.mp hk1).2.symm.trans (Finset.mem_filter.mp hk2).2)

private theorem sum_hi_le {X : ℕ} (hX : 0 < X)
    (hu_half_pos : 0 < Real.log (X : ℝ) - 1 / 2) :
    (∑ k ∈ Finset.range X, hiSliceVal X ((256 * k) / X)) ≤
      ((X / 256 + 1 : ℕ) : ℝ) * ((1410268367 : ℝ) / 10000000) *
        ((X : ℝ) / (Real.log (X : ℝ) - 1 / 2)) := by
  conv_lhs => rw [← range_biUnion_fibers hX]
  rw [Finset.sum_biUnion fibers_pairwiseDisjoint]
  have hterm : ∀ s ∈ Finset.range 256,
      (∑ k ∈ (Finset.range X).filter (fun k => (256 * k) / X = s),
        hiSliceVal X ((256 * k) / X)) ≤
        ((X / 256 + 1 : ℕ) : ℝ) * hiSliceVal X s := by
    intro s hs
    have heq : ∀ k ∈ (Finset.range X).filter (fun k => (256 * k) / X = s),
        hiSliceVal X ((256 * k) / X) = hiSliceVal X s := by
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Finset.range X).filter (fun k => (256 * k) / X = s)).card : ℝ) ≤
        ((X / 256 + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (fiber_card_bounds hX (Finset.mem_range.mp hs)).2
    have hnonneg : 0 ≤ hiSliceVal X s :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
        (div_nonneg (Nat.cast_nonneg _) hu_half_pos.le)
    exact mul_le_mul_of_nonneg_right hcard hnonneg
  calc
    (∑ s ∈ Finset.range 256, ∑ k ∈ (Finset.range X).filter (fun k => (256 * k) / X = s),
        hiSliceVal X ((256 * k) / X))
      ≤ ∑ s ∈ Finset.range 256, ((X / 256 + 1 : ℕ) : ℝ) * hiSliceVal X s := Finset.sum_le_sum hterm
    _ = ((X / 256 + 1 : ℕ) : ℝ) * ∑ s ∈ Finset.range 256, hiSliceVal X s := by
        rw [← Finset.mul_sum]
    _ = ((X / 256 + 1 : ℕ) : ℝ) * ((1410268367 : ℝ) / 10000000) *
          ((X : ℝ) / (Real.log (X : ℝ) - 1 / 2)) := by
        have hsum_cast : (∑ s ∈ Finset.range 256, (hiCoeff s : ℝ)) = 1410268367 := by
          exact_mod_cast sum_hiCoeff_eq
        dsimp [hiSliceVal]
        simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← Finset.sum_mul, hsum_cast]
        ring

private theorem sum_lo_ge {X : ℕ} (hX : 0 < X)
    (hu_three_pos : 0 < Real.log (X : ℝ) - 3 / 2) :
    ((X / 256 : ℕ) : ℝ) * ((1231373994 : ℝ) / 10000000) *
        ((X : ℝ) / (Real.log (X : ℝ) - 3 / 2)) - (X : ℝ) ≤
      ∑ k ∈ Finset.range X, loSliceVal X ((256 * k) / X) := by
  let posSlice : ℕ → ℝ := fun s =>
    (loCoeff s : ℝ) / 10000000 * ((X : ℝ) / (Real.log (X : ℝ) - 3 / 2))
  have hlo_ge : ∀ k ∈ Finset.range X, posSlice ((256 * k) / X) - 1 ≤ loSliceVal X ((256 * k) / X) := by
    intro k _
    dsimp [loSliceVal, posSlice]
    split_ifs with hs0
    · rw [hs0, loCoeff_zero]
      norm_num
    · exact le_rfl
  have h1 : (∑ k ∈ Finset.range X, posSlice ((256 * k) / X)) - (X : ℝ) ≤
      ∑ k ∈ Finset.range X, loSliceVal X ((256 * k) / X) := by
    have hsum := Finset.sum_le_sum hlo_ge
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
    exact hsum
  have hsplit : (∑ k ∈ Finset.range X, posSlice ((256 * k) / X)) =
      ∑ s ∈ Finset.range 256, ∑ k ∈ (Finset.range X).filter (fun k => (256 * k) / X = s),
        posSlice ((256 * k) / X) := by
    conv_lhs => rw [← range_biUnion_fibers hX]
    exact Finset.sum_biUnion fibers_pairwiseDisjoint
  have hterm : ∀ s ∈ Finset.range 256,
      ((X / 256 : ℕ) : ℝ) * posSlice s ≤
        ∑ k ∈ (Finset.range X).filter (fun k => (256 * k) / X = s), posSlice ((256 * k) / X) := by
    intro s hs
    have heq : ∀ k ∈ (Finset.range X).filter (fun k => (256 * k) / X = s),
        posSlice ((256 * k) / X) = posSlice s := by
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((X / 256 : ℕ) : ℝ) ≤
        (((Finset.range X).filter (fun k => (256 * k) / X = s)).card : ℝ) :=
      Nat.cast_le.mpr (fiber_card_bounds hX (Finset.mem_range.mp hs)).1
    have hnonneg : 0 ≤ posSlice s :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
        (div_nonneg (Nat.cast_nonneg _) hu_three_pos.le)
    exact mul_le_mul_of_nonneg_right hcard hnonneg
  have h2 : ((X / 256 : ℕ) : ℝ) * ((1231373994 : ℝ) / 10000000) *
      ((X : ℝ) / (Real.log (X : ℝ) - 3 / 2)) ≤
      ∑ s ∈ Finset.range 256, ∑ k ∈ (Finset.range X).filter (fun k => (256 * k) / X = s),
        posSlice ((256 * k) / X) := by
    calc
      ((X / 256 : ℕ) : ℝ) * ((1231373994 : ℝ) / 10000000) * ((X : ℝ) / (Real.log (X : ℝ) - 3 / 2))
        = ((X / 256 : ℕ) : ℝ) * ∑ s ∈ Finset.range 256, posSlice s := by
            have hsum_cast : (∑ s ∈ Finset.range 256, (loCoeff s : ℝ)) = 1231373994 := by
              exact_mod_cast sum_loCoeff_eq
            dsimp [posSlice]
            simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← Finset.sum_mul, hsum_cast]
            ring
      _ = ∑ s ∈ Finset.range 256, ((X / 256 : ℕ) : ℝ) * posSlice s := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum hterm
  linarith

/-- Global prescribed-pool normalized mean bounds for EVERY order `n ≥ 2001` (unbounded above):
    `449 / 1000 < m / X` and `m / X < 519 / 1000`. -/
theorem global_pool_mean_bounds
    (rs : RSPrimeCountImports) (sharp : RSIndexLowerSharp)
    {n : ℕ} (hn : 2001 ≤ n) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    (449 / 1000 : ℝ) < ((Lucas.poolTotal n : ℝ) / N) / X ∧
    ((Lucas.poolTotal n : ℝ) / N) / X < (519 / 1000 : ℝ) := by
  dsimp only
  obtain ⟨hXnat_gt, hu_gt⟩ := poolMaximum_gt_65170000_and_log_gt sharp hn
  let Xnat := poolMaximum n
  change (449 / 1000 : ℝ) < ((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) / (Xnat : ℝ) ∧
    ((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) / (Xnat : ℝ) < (519 / 1000 : ℝ)
  have hXnat_gt' : 65170000 < Xnat := hXnat_gt
  have hu_gt' : (178 / 10 : ℝ) < Real.log (Xnat : ℝ) := hu_gt
  have hXnat_pos : 0 < Xnat := by omega
  have hX_gt : (65170000 : ℝ) < (Xnat : ℝ) := Nat.cast_lt.mpr hXnat_gt'
  have hX_pos : 0 < (Xnat : ℝ) := by linarith
  have hN_ge : (4004001 : ℝ) ≤ ((n * n : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.mul_le_mul hn hn)
  have hN_pos : 0 < ((n * n : ℕ) : ℝ) := by linarith
  have hNX_pos : 0 < ((n * n : ℕ) : ℝ) * (Xnat : ℝ) := mul_pos hN_pos hX_pos
  have hu_half_pos : 0 < Real.log (Xnat : ℝ) - 1 / 2 := by linarith
  have hu_three_pos : 0 < Real.log (Xnat : ℝ) - 3 / 2 := by linarith

  have hpiX : primeCountReal (Xnat : ℝ) = ((n * n : ℕ) : ℝ) + 1 := by
    rw [primeCountReal_natCast_eq_oddPrefix_add_one (by omega : 2 ≤ Xnat)]
    dsimp [Xnat]
    rw [oddPrimePrefix_poolMaximum_card]
  have hN_lo : (Xnat : ℝ) / (Real.log (Xnat : ℝ) - 1 / 2) <
      (4004002 / 4004001 : ℝ) * ((n * n : ℕ) : ℝ) := by
    have h1 : (Xnat : ℝ) / (Real.log (Xnat : ℝ) - 1 / 2) < ((n * n : ℕ) : ℝ) + 1 := by
      rw [← hpiX]
      exact rs.lower_sharp (Xnat : ℝ) (by linarith)
    linarith
  have hN_hi : ((n * n : ℕ) : ℝ) < (Xnat : ℝ) / (Real.log (Xnat : ℝ) - 3 / 2) := by
    have hexp : Real.exp (3 / 2 : ℝ) < (Xnat : ℝ) := by linarith [exp_three_halves_lt_nine]
    have h2 : ((n * n : ℕ) : ℝ) + 1 < (Xnat : ℝ) / (Real.log (Xnat : ℝ) - 3 / 2) := by
      rw [← hpiX]
      exact rs.upper_sharp (Xnat : ℝ) hexp
    linarith

  let hi : ℕ → ℝ := fun k => hiSliceVal Xnat ((256 * k) / Xnat)
  let lo : ℕ → ℝ := fun k => loSliceVal Xnat ((256 * k) / Xnat)
  have hhi_env : ∀ k < Xnat, ((oddPrimePrefix k).card : ℝ) ≤ hi k :=
    fun _ hk => hi_envelope_le rs hXnat_gt' hu_gt' hk
  have hlo_env : ∀ k < Xnat, lo k ≤ ((oddPrimePrefix k).card : ℝ) :=
    fun _ hk => lo_envelope_ge rs hXnat_gt' hu_gt' hk
  have hsum_hi := sum_hi_le hXnat_pos hu_half_pos
  have hsum_lo := sum_lo_ge hXnat_pos hu_three_pos

  have henv := oddPrimePool_mean_bounds_of_count_envelopes n (by omega) lo hi hlo_env hhi_env
  change (1 - (∑ k ∈ Finset.range Xnat, hi k) / (((n * n : ℕ) : ℝ) * (Xnat : ℝ)) ≤
      ((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) / (Xnat : ℝ)) ∧
    (((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) / (Xnat : ℝ) ≤
      1 - (∑ k ∈ Finset.range Xnat, lo k) / (((n * n : ℕ) : ℝ) * (Xnat : ℝ))) at henv

  have hXdiv_hi : ((Xnat / 256 + 1 : ℕ) : ℝ) ≤ (65170256 / 65170000 : ℝ) * ((Xnat : ℝ) / 256) := by
    have hdiv_le : (((Xnat / 256) * 256 : ℕ) : ℝ) ≤ (Xnat : ℝ) :=
      Nat.cast_le.mpr (Nat.div_mul_le_self Xnat 256)
    push_cast at hdiv_le ⊢
    linarith
  have hXdiv_lo : (65169744 / 65170000 : ℝ) * ((Xnat : ℝ) / 256) ≤ ((Xnat / 256 : ℕ) : ℝ) := by
    have h1 := Nat.div_add_mod Xnat 256
    have h2 : Xnat % 256 < 256 := Nat.mod_lt Xnat (by norm_num)
    have h3 : Xnat ≤ (Xnat / 256) * 256 + 255 := by omega
    have h4 : (Xnat : ℝ) ≤ (((Xnat / 256) * 256 + 255 : ℕ) : ℝ) := Nat.cast_le.mpr h3
    push_cast at h4
    linarith

  constructor
  · have hhi_prod : (∑ k ∈ Finset.range Xnat, hi k) <
        (551 / 1000 : ℝ) * (((n * n : ℕ) : ℝ) * (Xnat : ℝ)) := by
      have hm1 : ((Xnat / 256 + 1 : ℕ) : ℝ) * ((1410268367 : ℝ) / 10000000) ≤
          ((65170256 / 65170000 : ℝ) * ((Xnat : ℝ) / 256)) * ((1410268367 : ℝ) / 10000000) :=
        mul_le_mul_of_nonneg_right hXdiv_hi (by norm_num)
      have hm2 := mul_lt_mul_of_pos_left hN_lo
        (mul_pos (mul_pos (by norm_num) (div_pos hX_pos (by norm_num))) (by norm_num) :
          0 < ((65170256 / 65170000 : ℝ) * ((Xnat : ℝ) / 256)) * ((1410268367 : ℝ) / 10000000))
      have h1 : ((Xnat / 256 + 1 : ℕ) : ℝ) * ((1410268367 : ℝ) / 10000000) *
            ((Xnat : ℝ) / (Real.log (Xnat : ℝ) - 1 / 2)) <
          ((65170256 / 65170000 : ℝ) * ((Xnat : ℝ) / 256)) * ((1410268367 : ℝ) / 10000000) *
            ((4004002 / 4004001 : ℝ) * ((n * n : ℕ) : ℝ)) :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hm1 (div_nonneg hX_pos.le hu_half_pos.le)) hm2
      have hconst : (65170256 / 65170000 : ℝ) * (1 / 256) * (1410268367 / 10000000) *
          (4004002 / 4004001) < 551 / 1000 := by norm_num
      have heq : ((65170256 / 65170000 : ℝ) * ((Xnat : ℝ) / 256)) * ((1410268367 : ℝ) / 10000000) *
          ((4004002 / 4004001 : ℝ) * ((n * n : ℕ) : ℝ)) =
          ((65170256 / 65170000 : ℝ) * (1 / 256) * (1410268367 / 10000000) *
            (4004002 / 4004001)) * (((n * n : ℕ) : ℝ) * (Xnat : ℝ)) := by ring
      have h2 := mul_lt_mul_of_pos_right hconst hNX_pos
      change (∑ k ∈ Finset.range Xnat, hiSliceVal Xnat ((256 * k) / Xnat)) < _
      linarith
    have hdiv := (div_lt_iff₀ hNX_pos).mpr hhi_prod
    linarith [henv.1]
  · have hlo_prod : (481 / 1000 : ℝ) * (((n * n : ℕ) : ℝ) * (Xnat : ℝ)) <
        ∑ k ∈ Finset.range Xnat, lo k := by
      have hm1 : ((65169744 / 65170000 : ℝ) * ((Xnat : ℝ) / 256)) * ((1231373994 : ℝ) / 10000000) ≤
          ((Xnat / 256 : ℕ) : ℝ) * ((1231373994 : ℝ) / 10000000) :=
        mul_le_mul_of_nonneg_right hXdiv_lo (by norm_num)
      have hm2 := mul_lt_mul_of_pos_left hN_hi
        (mul_pos (mul_pos (by norm_num) (div_pos hX_pos (by norm_num))) (by norm_num) :
          0 < ((65169744 / 65170000 : ℝ) * ((Xnat : ℝ) / 256)) * ((1231373994 : ℝ) / 10000000))
      have h1 : ((65169744 / 65170000 : ℝ) * ((Xnat : ℝ) / 256)) * ((1231373994 : ℝ) / 10000000) *
            ((n * n : ℕ) : ℝ) <
          ((Xnat / 256 : ℕ) : ℝ) * ((1231373994 : ℝ) / 10000000) *
            ((Xnat : ℝ) / (Real.log (Xnat : ℝ) - 3 / 2)) :=
        lt_of_lt_of_le hm2 (mul_le_mul_of_nonneg_right hm1 (div_nonneg hX_pos.le hu_three_pos.le))
      have hX_le : (Xnat : ℝ) ≤ (1 / 4004001 : ℝ) * (((n * n : ℕ) : ℝ) * (Xnat : ℝ)) := by
        have hmulN := mul_le_mul_of_nonneg_right hN_ge hX_pos.le
        linarith
      have hconst : (481 / 1000 : ℝ) + (1 / 4004001 : ℝ) <
          (65169744 / 65170000 : ℝ) * (1 / 256) * (1231373994 / 10000000) := by norm_num
      have heq : ((65169744 / 65170000 : ℝ) * ((Xnat : ℝ) / 256)) * ((1231373994 : ℝ) / 10000000) *
          ((n * n : ℕ) : ℝ) =
          ((65169744 / 65170000 : ℝ) * (1 / 256) * (1231373994 / 10000000)) *
            (((n * n : ℕ) : ℝ) * (Xnat : ℝ)) := by ring
      have hmul := mul_lt_mul_of_pos_right hconst hNX_pos
      change _ < ∑ k ∈ Finset.range Xnat, loSliceVal Xnat ((256 * k) / Xnat)
      linarith
    have hdiv := (lt_div_iff₀ hNX_pos).mpr hlo_prod
    linarith [henv.2]

end

end Sude
