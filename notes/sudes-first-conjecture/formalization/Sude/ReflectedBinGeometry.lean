import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Geometry of finite reflected half-open bins, with exact endpoints. -/
namespace Sude
noncomputable section

/-- Left endpoint of a lower bin or its reflected upper bin. -/
def reflectedBinLeft {N : ℕ} (L U t : ℝ) (z : Fin N × Bool) : ℝ :=
  if z.2 then U - ((z.1.val : ℝ) + 1) * t else L + (z.1.val : ℝ) * t

/-- Right endpoint of a lower bin or its reflected upper bin. -/
def reflectedBinRight {N : ℕ} (L U t : ℝ) (z : Fin N × Bool) : ℝ :=
  if z.2 then U - (z.1.val : ℝ) * t else L + ((z.1.val : ℝ) + 1) * t

/-- All reflected-bin endpoints lie in `[1,X]` and each interval has
nonnegative length, provided the two complete bands are separated. -/
theorem reflected_bin_endpoint_bounds {N : ℕ} (L U t X : ℝ)
    (hL : 1 ≤ L) (ht : 0 < t) (hsep : L + N * t ≤ U - N * t) (hU : U ≤ X) :
    ∀ z : Fin N × Bool, 1 ≤ reflectedBinLeft L U t z ∧
      reflectedBinLeft L U t z ≤ reflectedBinRight L U t z ∧
      reflectedBinRight L U t z ≤ X := by
  rintro ⟨i, side⟩
  have hi : ((i.val : ℝ) + 1) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hiT := mul_le_mul_of_nonneg_right hi (le_of_lt ht)
  have hi0 : 0 ≤ (i.val : ℝ) * t := by positivity
  have hNT : 0 ≤ (N : ℝ) * t := by positivity
  cases side <;> simp only [reflectedBinLeft, reflectedBinRight, Bool.false_eq_true,
    ↓reduceIte] <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- Distinct reflected half-open bins are separated, including opposite
bands and the reversed upper-bin order. -/
theorem reflected_bin_pairwise_separated {N : ℕ} (L U t : ℝ)
    (ht : 0 < t) (hsep : L + N * t ≤ U - N * t) :
    ∀ z w : Fin N × Bool, z ≠ w →
      reflectedBinRight L U t z ≤ reflectedBinLeft L U t w ∨
      reflectedBinRight L U t w ≤ reflectedBinLeft L U t z := by
  rintro ⟨i, si⟩ ⟨j, sj⟩ hne
  have hi : ((i.val : ℝ) + 1) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hj : ((j.val : ℝ) + 1) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
  have hiT := mul_le_mul_of_nonneg_right hi (le_of_lt ht)
  have hjT := mul_le_mul_of_nonneg_right hj (le_of_lt ht)
  have hi0 : 0 ≤ (i.val : ℝ) * t := by positivity
  have hj0 : 0 ≤ (j.val : ℝ) * t := by positivity
  cases si <;> cases sj
  · have hij : i ≠ j := by intro heq; subst j; exact hne rfl
    rcases lt_or_gt_of_ne hij with h | h
    · left
      have hk : ((i.val : ℝ) + 1) ≤ j.val := by exact_mod_cast (Nat.succ_le_of_lt h)
      have hkt := mul_le_mul_of_nonneg_right hk (le_of_lt ht)
      simp only [reflectedBinLeft, reflectedBinRight, Bool.false_eq_true, ↓reduceIte]
      linarith
    · right
      have hk : ((j.val : ℝ) + 1) ≤ i.val := by exact_mod_cast (Nat.succ_le_of_lt h)
      have hkt := mul_le_mul_of_nonneg_right hk (le_of_lt ht)
      simp only [reflectedBinLeft, reflectedBinRight, Bool.false_eq_true, ↓reduceIte]
      linarith
  · left
    simp only [reflectedBinLeft, reflectedBinRight, Bool.false_eq_true, ↓reduceIte]
    linarith
  · right
    simp only [reflectedBinLeft, reflectedBinRight, Bool.false_eq_true, ↓reduceIte]
    linarith
  · have hij : i ≠ j := by intro heq; subst j; exact hne rfl
    rcases lt_or_gt_of_ne hij with h | h
    · right
      have hk : ((i.val : ℝ) + 1) ≤ j.val := by exact_mod_cast (Nat.succ_le_of_lt h)
      have hkt := mul_le_mul_of_nonneg_right hk (le_of_lt ht)
      simp only [reflectedBinLeft, reflectedBinRight, ↓reduceIte]
      linarith
    · left
      have hk : ((j.val : ℝ) + 1) ≤ i.val := by exact_mod_cast (Nat.succ_le_of_lt h)
      have hkt := mul_le_mul_of_nonneg_right hk (le_of_lt ht)
      simp only [reflectedBinLeft, reflectedBinRight, ↓reduceIte]
      linarith

/-- Every lower bin lies to the left of every upper bin. -/
theorem reflected_bin_cross_separated {N : ℕ} (L U t : ℝ)
    (ht : 0 < t) (hsep : L + N * t ≤ U - N * t) :
    ∀ i j : Fin N, reflectedBinRight L U t (i, false) ≤ reflectedBinLeft L U t (j, true) := by
  intro i j
  have hi : ((i.val : ℝ) + 1) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hj : ((j.val : ℝ) + 1) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
  have hiT := mul_le_mul_of_nonneg_right hi (le_of_lt ht)
  have hjT := mul_le_mul_of_nonneg_right hj (le_of_lt ht)
  simp only [reflectedBinLeft, reflectedBinRight, Bool.false_eq_true, ↓reduceIte]
  linarith

/-- A pair in matched reflected bins has the exact midpoint error and global
gap interval. Half-open endpoints are retained in the hypotheses. -/
theorem reflected_bin_pair_bounds {N : ℕ} (L U t : ℝ) (ht : 0 < t)
    (i : Fin N) (p q : ℝ)
    (hp : reflectedBinLeft L U t (i, false) < p ∧ p ≤ reflectedBinRight L U t (i, false))
    (hq : reflectedBinLeft L U t (i, true) < q ∧ q ≤ reflectedBinRight L U t (i, true)) :
    |(p + q) / 2 - (L + U) / 2| ≤ t / 2 ∧
      U - L - 2 * N * t ≤ q - p ∧ q - p ≤ U - L := by
  have hi : ((i.val : ℝ) + 1) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hiT := mul_le_mul_of_nonneg_right hi (le_of_lt ht)
  have hi0 : 0 ≤ (i.val : ℝ) * t := by positivity
  simp only [reflectedBinLeft, reflectedBinRight, Bool.false_eq_true, ↓reduceIte] at hp hq
  constructor
  · apply abs_le.mpr
    constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  · constructor <;> nlinarith [hp.1, hp.2, hq.1, hq.2]

end
end Sude
