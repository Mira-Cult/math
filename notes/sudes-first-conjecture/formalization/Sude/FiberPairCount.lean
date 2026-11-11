import Sude.FixedGapMatching
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast

/-! Exact finite pair counts for bins and residue classes. -/
namespace Sude
noncomputable section

/-- Ordered distinct elements in one class are represented once, by their
increasing pair. -/
def sameClassPairs {K : Type*} [DecidableEq K] (S : Finset ℕ) (key : ℕ → K) : Finset (ℕ × ℕ) :=
  (S.product S).filter fun z => z.1 < z.2 ∧ key z.1 = key z.2

/-- The number of within-class pairs is exactly the sum of `choose 2` over
all actual nonempty fibers. -/
theorem sameClassPairs_card {K : Type*} [DecidableEq K] (S : Finset ℕ) (key : ℕ → K) :
    (sameClassPairs S key).card = ∑ c ∈ S.image key, (S.filter (fun p => key p = c)).card.choose 2 := by
  classical
  have hmap : ∀ z ∈ sameClassPairs S key, key z.1 ∈ S.image key := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).1
    exact Finset.mem_image.mpr ⟨z.1, (Finset.mem_product.mp hz').1, rfl⟩
  have hc := Finset.card_eq_sum_card_fiberwise (s := sameClassPairs S key) (t := S.image key)
    (f := fun z : ℕ × ℕ => key z.1) hmap
  rw [hc]
  apply Finset.sum_congr rfl
  intro c hc'
  let F := S.filter fun p => key p = c
  have hset : (sameClassPairs S key).filter (fun z => key z.1 = c) =
      (F.product F).filter (fun z => z.1 < z.2) := by
    ext ⟨p, q⟩
    simp only [sameClassPairs, Finset.mem_filter, F]
    aesop
  rw [hset]
  change ((F ×ˢ F).filter (fun z => z.1 < z.2)).card = F.card.choose 2
  exact Finset.card_product_filter_lt

/-- Cauchy--Schwarz for the actual within-class pairs. `B` may be any
upper bound on the number of nonempty classes, including zero. -/
theorem sameClassPairs_cauchy {K : Type*} [DecidableEq K] (S : Finset ℕ)
    (key : ℕ → K) (B : ℕ) (hB : (S.image key).card ≤ B) :
    (S.card : ℝ) ^ 2 ≤ (B : ℝ) * (2 * (sameClassPairs S key).card + S.card) := by
  classical
  let C := S.image key
  let count : K → ℝ := fun c => (S.filter (fun p => key p = c)).card
  have hsum : (∑ c ∈ C, count c) = S.card := by
    have h := Finset.card_eq_sum_card_image key S
    dsimp [C, count]
    exact_mod_cast h.symm
  have hchoose : ((sameClassPairs S key).card : ℝ) =
      ∑ c ∈ C, (((S.filter (fun p => key p = c)).card.choose 2 : ℕ) : ℝ) := by
    exact_mod_cast sameClassPairs_card S key
  have hsumsq : 2 * ((sameClassPairs S key).card : ℝ) + S.card =
      ∑ c ∈ C, (count c) ^ 2 := by
    rw [hchoose, ← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Nat.cast_choose_two ℝ]
    dsimp [count]
    ring
  have hCS : (S.card : ℝ) ^ 2 ≤
      (2 * (sameClassPairs S key).card + S.card) * C.card := by
    calc
      _ = (∑ c ∈ C, count c * (1 : ℝ)) ^ 2 := by simp [hsum]
      _ ≤ (∑ c ∈ C, (count c) ^ 2) * ∑ c ∈ C, (1 : ℝ) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq C count (fun _ => 1)
      _ = _ := by rw [← hsumsq]; simp
  have hBR : (C.card : ℝ) ≤ B := by exact_mod_cast hB
  have hmul := mul_le_mul_of_nonneg_left hBR (show (0 : ℝ) ≤ 2 * (sameClassPairs S key).card + S.card by positivity)
  nlinarith [hCS, hmul]

/-- The corresponding divided form of the finite pair bound, with positive
class count stated explicitly. -/
theorem sameClassPairs_lower_bound {K : Type*} [DecidableEq K] (S : Finset ℕ)
    (key : ℕ → K) (B : ℕ) (hB : (S.image key).card ≤ B) (hpos : 0 < B) :
    ((S.card : ℝ) ^ 2 / B - S.card) / 2 ≤ (sameClassPairs S key).card := by
  have h := sameClassPairs_cauchy S key B hB
  have hBR : (0 : ℝ) < B := by exact_mod_cast hpos
  have hd : (S.card : ℝ) ^ 2 / B ≤ 2 * (sameClassPairs S key).card + S.card :=
    (div_le_iff₀ hBR).2 (by nlinarith [h])
  linarith

end
end Sude
