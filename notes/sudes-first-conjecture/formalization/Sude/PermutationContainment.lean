import Sude.PermutationSampling
import Mathlib.Data.Nat.Factorial.BigOperators

/-! Without-replacement containment estimates for specified permutation images. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- The event that a permutation maps every specified input into `S`. -/
def permutationContainmentEvent {n : ℕ} (J S : Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p => J.image p ⊆ S)

/-- Exact number of permutations mapping the specified positions into `S`,
with all images sampled without replacement. -/
theorem permutationContainment_exact {n : ℕ} (J S : Finset (Fin n)) :
    Nat.choose n J.card * (permutationContainmentEvent J S).card =
      n.factorial * Nat.choose S.card J.card := by
  classical
  let targets := S.powersetCard J.card
  have htargets : ∀ T ∈ targets, T.card = J.card := by
    intro T hT
    exact (Finset.mem_powersetCard.mp hT).2
  have hevent : permutationImageEvent J targets = permutationContainmentEvent J S := by
    ext p
    simp only [permutationImageEvent, permutationContainmentEvent, Finset.mem_filter,
      Finset.mem_univ, true_and, targets, Finset.mem_powersetCard]
    rw [Finset.card_image_of_injective _ p.injective]
    simp
  have h := permutation_image_uniform J targets htargets
  rw [hevent] at h
  simpa [targets, Finset.card_powersetCard] using h

/-- Product form of `(s)_j / (n)_j ≤ (s/n)^j`; no division is used. -/
theorem descFactorial_ratio_power {n s j : ℕ} (hs : s ≤ n) (hj : j ≤ s) :
    n^j * s.descFactorial j ≤ s^j * n.descFactorial j := by
  have hfactor (i : ℕ) (hi : i ∈ Finset.range j) :
      n * (s - i) ≤ s * (n - i) := by
    have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
    have hin : i ≤ n := by omega
    have hs' := Nat.sub_add_cancel his
    have hn' := Nat.sub_add_cancel hin
    nlinarith
  calc
    _ = ∏ i ∈ Finset.range j, n * (s - i) := by
      rw [Finset.prod_mul_distrib, Nat.descFactorial_eq_prod_range]
      simp
    _ ≤ ∏ i ∈ Finset.range j, s * (n - i) := by
      apply Finset.prod_le_prod'
      exact hfactor
    _ = _ := by
      rw [Finset.prod_mul_distrib, Nat.descFactorial_eq_prod_range]
      simp

/-- Binomial-coefficient version of the same bound. -/
theorem choose_ratio_power {n s j : ℕ} (hs : s ≤ n) (hj : j ≤ s) :
    n^j * s.choose j ≤ s^j * n.choose j := by
  have h := descFactorial_ratio_power hs hj
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hfact : 0 < j.factorial := Nat.factorial_pos j
  apply Nat.le_of_mul_le_mul_left (c := j.factorial) _ hfact
  nlinarith

/-- The fixed-containment event has probability at most `(s/n)^j`, in an
integer form that also handles zero denominators without hidden conventions. -/
theorem permutationContainment_power_bound {n : ℕ} (J S : Finset (Fin n))
    (hJS : J.card ≤ S.card) :
    n^J.card * (permutationContainmentEvent J S).card ≤ n.factorial * S.card^J.card := by
  have hsn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hjn : J.card ≤ n := hJS.trans hsn
  have hC : 0 < n.choose J.card := Nat.choose_pos hjn
  have hexact := permutationContainment_exact J S
  have hratio := choose_ratio_power hsn hJS
  apply Nat.le_of_mul_le_mul_left (c := n.choose J.card) _ hC
  calc
    _ = n^J.card * (n.choose J.card * (permutationContainmentEvent J S).card) := by ring
    _ = n^J.card * (n.factorial * S.card.choose J.card) := by rw [hexact]
    _ = n.factorial * (n^J.card * S.card.choose J.card) := by ring
    _ ≤ n.factorial * (S.card^J.card * n.choose J.card) := Nat.mul_le_mul_left _ hratio
    _ = _ := by ring

/-- Each independent permutation must map its own specified positions into
the same cut. -/
def permutationFamilyContainmentEvent {r n : ℕ} (J : Fin r → Finset (Fin n))
    (S : Finset (Fin n)) : Finset (Fin r → Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p => ∀ i, (J i).image (p i) ⊆ S)

/-- The independent whole-permutation sample is the product of the exact
within-permutation containment events. -/
theorem permutationFamilyContainment_card {r n : ℕ} (J : Fin r → Finset (Fin n))
    (S : Finset (Fin n)) :
    (permutationFamilyContainmentEvent J S).card =
      ∏ i, (permutationContainmentEvent (J i) S).card := by
  classical
  have hset : permutationFamilyContainmentEvent J S =
      Fintype.piFinset (fun i => permutationContainmentEvent (J i) S) := by
    ext p
    simp [permutationFamilyContainmentEvent, permutationContainmentEvent, Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset]

/-- For independent permutations, specified-image containment has the
product of the without-replacement bounds, in exact integer form. -/
theorem permutationFamilyContainment_power_bound {r n : ℕ} (J : Fin r → Finset (Fin n))
    (S : Finset (Fin n)) (hJS : ∀ i, (J i).card ≤ S.card) :
    n^(∑ i, (J i).card) * (permutationFamilyContainmentEvent J S).card ≤
      n.factorial^r * S.card^(∑ i, (J i).card) := by
  classical
  rw [permutationFamilyContainment_card]
  calc
    _ = ∏ i : Fin r, (n^(J i).card * (permutationContainmentEvent (J i) S).card) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ i : Fin r, (n.factorial * S.card^(J i).card) := by
      apply Finset.prod_le_prod'
      intro i hi
      exact permutationContainment_power_bound (J i) S (hJS i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp

end
end Sude
