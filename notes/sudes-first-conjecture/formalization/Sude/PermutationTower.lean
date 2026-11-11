import Sude.PermutationHoeffding

/-! Finite tower decomposition for successive permutation histories. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance towerPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Partition a history by the next output. This is the exact finite tower
identity underlying sequential conditioning. -/
theorem permutationHistory_sum_by_next {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (F : Equiv.Perm (Fin n) → ℝ) :
    (∑ p ∈ permutationHistory positions reference, F p) =
      ∑ a ∈ (positions.image reference)ᶜ,
        ∑ p ∈ permutationHistoryNext positions reference i a, F p := by
  classical
  have hmap : ∀ p ∈ permutationHistory positions reference,
      p i ∈ (positions.image reference)ᶜ := by
    intro p hp
    simpa using permutationHistory_next_unused positions reference p i hi hp
  symm
  exact Finset.sum_fiberwise_of_maps_to hmap F

/-- Select a completion of any unused next value. Existence is proved by
finite-fiber positivity, not assumed as an external oracle. -/
def permutationHistoryExtension {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (a : {a // a ∈ (positions.image reference)ᶜ}) : Equiv.Perm (Fin n) :=
  Classical.choose (Finset.card_pos.mp (permutationHistoryNext_card_pos positions reference i a.val hi
    (Finset.mem_compl.mp a.property)))

theorem permutationHistoryExtension_mem {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (a : {a // a ∈ (positions.image reference)ᶜ}) :
    permutationHistoryExtension positions reference i hi a ∈
      permutationHistoryNext positions reference i a.val :=
  Classical.choose_spec (Finset.card_pos.mp (permutationHistoryNext_card_pos positions reference i a.val hi
    (Finset.mem_compl.mp a.property)))

/-- Exact tower property for the uniform history measure: averaging the
future conditional means over all unused next values recovers the current
conditional mean. -/
theorem permutationHistory_integral_tower {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (F : Equiv.Perm (Fin n) → ℝ) :
    (permutationHistoryMeasure positions reference)[F] =
      (∑ a ∈ ((positions.image reference)ᶜ).attach,
        (permutationHistoryMeasure (insert i positions)
          (permutationHistoryExtension positions reference i hi a))[F]) / ((n - positions.card : ℕ) : ℝ) := by
  classical
  let available : Finset (Fin n) := (positions.image reference)ᶜ
  let history := permutationHistory positions reference
  let c := (permutationHistoryNext positions reference i (reference i)).card
  have ha : reference i ∉ positions.image reference :=
    permutationHistory_next_unused positions reference reference i hi (by simp [permutationHistory])
  have hcpos : 0 < c := permutationHistoryNext_card_pos positions reference i (reference i) hi ha
  have hKpos : 0 < n - positions.card := by
    have hlt : positions.card < n := by simpa using Finset.card_lt_univ_of_notMem hi
    omega
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcpos)
  have hK0 : ((n - positions.card : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hKpos)
  have hcard : (history.card : ℝ) = ((n - positions.card : ℕ) : ℝ) * c := by
    exact_mod_cast (permutationHistory_next_uniform positions reference i (reference i) hi ha).symm
  have hH0 : (history.card : ℝ) ≠ 0 := by rw [hcard]; exact mul_ne_zero hK0 hc0
  have hterm (a : {a // a ∈ available}) :
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[F] =
      (∑ p ∈ permutationHistoryNext positions reference i a.val, F p) / (c : ℝ) := by
    have hm := permutationHistoryExtension_mem positions reference i hi a
    have heq := permutationHistoryNext_eq_insert positions reference
      (permutationHistoryExtension positions reference i hi a) i a.val hm
    rw [permutationHistory_integral, ← heq]
    have hcount := permutationHistoryNext_card_eq positions reference i a.val (reference i)
      (Finset.mem_compl.mp a.property) ha
    rw [hcount]
  change (permutationHistoryMeasure positions reference)[F] =
    (∑ a ∈ available.attach,
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[F]) / ((n - positions.card : ℕ) : ℝ)
  rw [permutationHistory_integral]
  have hsum : (∑ a ∈ available.attach,
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[F]) =
      (∑ p ∈ history, F p) / (c : ℝ) := by
    calc
      _ = ∑ a ∈ available.attach,
          ((∑ p ∈ permutationHistoryNext positions reference i a.val, F p) / (c : ℝ)) := by
        apply Finset.sum_congr rfl
        intro a ha'
        exact hterm a
      _ = (∑ a ∈ available.attach,
          ∑ p ∈ permutationHistoryNext positions reference i a.val, F p) / (c : ℝ) := by
        rw [Finset.sum_div]
      _ = (∑ p ∈ history, F p) / (c : ℝ) := by
        have hatt : (∑ a ∈ available.attach,
            ∑ p ∈ permutationHistoryNext positions reference i a.val, F p) =
            ∑ a ∈ available, ∑ p ∈ permutationHistoryNext positions reference i a, F p := by
          exact Finset.sum_attach available (fun a =>
            ∑ p ∈ permutationHistoryNext positions reference i a, F p)
        rw [hatt]
        exact congrArg (fun x : ℝ => x / (c : ℝ))
          (permutationHistory_sum_by_next positions reference i hi F).symm
  rw [hsum, hcard]
  field_simp
  rfl

/-- A uniform upper bound on every next-history integral also bounds the
current-history integral. This is the finite expectation step for an
inductive moment argument. -/
theorem permutationHistory_integral_le_of_next {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (F : Equiv.Perm (Fin n) → ℝ) (C : ℝ)
    (hbound : ∀ a : {a // a ∈ (positions.image reference)ᶜ},
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[F] ≤ C) :
    (permutationHistoryMeasure positions reference)[F] ≤ C := by
  classical
  let available : Finset (Fin n) := (positions.image reference)ᶜ
  have hKpos : 0 < ((n - positions.card : ℕ) : ℝ) := by
    have hlt : positions.card < n := by simpa using Finset.card_lt_univ_of_notMem hi
    have hnat : 0 < n - positions.card := by omega
    exact_mod_cast hnat
  have hsum : (∑ a ∈ available.attach,
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[F]) ≤
        ((n - positions.card : ℕ) : ℝ) * C := by
    calc
      _ ≤ ∑ _a ∈ available.attach, C := by
        apply Finset.sum_le_sum
        intro a ha
        exact hbound a
      _ = _ := by
        simp [available, Finset.card_compl, Finset.card_image_of_injective _ reference.injective]
  rw [permutationHistory_integral_tower positions reference i hi F]
  apply (div_le_iff₀ hKpos).2
  simpa [mul_comm] using hsum

end
end Sude
