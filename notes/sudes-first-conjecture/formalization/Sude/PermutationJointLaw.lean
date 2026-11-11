import Sude.PermutationSampling
import Mathlib.Data.Fintype.BigOperators

/-! Joint outgoing-edge counts for independent uniform permutations. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- The event that each independently sampled permutation has its assigned
outgoing-edge count. -/
def permutationCountTupleEvent {r n : ℕ} (S : Finset (Fin n)) (j : Fin r → ℕ) :
    Finset (Fin r → Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p => ∀ i, (permutationOutgoing (p i) S).card = j i)

/-- The joint finite sample space is the Cartesian product of the individual
permutation events. -/
theorem permutationCountTupleEvent_card {r n : ℕ} (S : Finset (Fin n)) (j : Fin r → ℕ) :
    (permutationCountTupleEvent S j).card = ∏ i,
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun p => (permutationOutgoing p S).card = j i)).card := by
  classical
  have hset : permutationCountTupleEvent S j = Fintype.piFinset (fun i =>
      (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun p => (permutationOutgoing p S).card = j i)) := by
    ext p
    simp [permutationCountTupleEvent, Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset]

/-- Exact joint hypergeometric count. Independence is used between whole
uniform permutations; each permutation's image remains without replacement. -/
theorem permutationCountTuple_hypergeometric {r n : ℕ} (S : Finset (Fin n))
    (j : Fin r → ℕ) (hj : ∀ i, j i ≤ S.card) :
    (Nat.choose n S.card) ^ r * (permutationCountTupleEvent S j).card =
      (n.factorial) ^ r * ∏ i, (Nat.choose S.card (j i) * Nat.choose (n - S.card) (j i)) := by
  classical
  rw [permutationCountTupleEvent_card]
  calc
    _ = ∏ i : Fin r, (Nat.choose n S.card *
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun p => (permutationOutgoing p S).card = j i)).card) := by
          rw [Finset.prod_mul_distrib]
          simp
    _ = ∏ i : Fin r, (n.factorial *
        (Nat.choose S.card (j i) * Nat.choose (n - S.card) (j i))) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact permutation_outgoing_hypergeometric S (j i) (hj i)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp

/-- The outgoing edges of a labelled family are exactly the disjoint sum of
its individual outgoing counts. -/
theorem permutationFamily_outgoing_card {r n : ℕ} (p : Fin r → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    (permutationOutgoing (permutationFamilyEdgePerm p)
      (Finset.univ.filter (fun e : Fin r × Fin n => e.2 ∈ S))).card =
        ∑ i, (permutationOutgoing (p i) S).card := by
  classical
  let Q := permutationOutgoing (permutationFamilyEdgePerm p)
    (Finset.univ.filter (fun e : Fin r × Fin n => e.2 ∈ S))
  change Q.card = _
  have hmap : ∀ e ∈ Q, e.1 ∈ (Finset.univ : Finset (Fin r)) := by simp
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro i hi
  have hset : Q.filter (fun e => e.1 = i) =
      (permutationOutgoing (p i) S).image (fun x => (i, x)) := by
    ext ⟨k, x⟩
    simp only [Q, permutationOutgoing, Finset.mem_filter, Finset.mem_univ, true_and,
      permutationFamilyEdgePerm, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, hy⟩, rfl⟩
      exact ⟨x, ⟨hx, hy⟩, rfl, rfl⟩
    · rintro ⟨y, ⟨hy, hn⟩, rfl, rfl⟩
      exact ⟨⟨hy, hn⟩, rfl⟩
  rw [hset, Finset.card_image_of_injective _ (fun x y h => Prod.mk.inj h |>.2)]

/-- The routing cut is twice the sum of the individual outgoing counts. -/
theorem permutationFamily_cut_card_sum {r n : ℕ} (p : Fin r → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    (cutEdges (fun e : Fin r × Fin n => e.2) (fun e => p e.1 e.2) S).card =
      2 * ∑ i, (permutationOutgoing (p i) S).card := by
  rw [permutationFamily_cut_card, permutationFamily_outgoing_card]

/-- The finite tuple of outgoing counts for a permutation triple. -/
def permutationOutgoingTuple {n : ℕ} (S : Finset (Fin n))
    (p : Fin 3 → Equiv.Perm (Fin n)) : Fin 3 → Fin (S.card + 1) :=
  fun i => ⟨(permutationOutgoing (p i) S).card,
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))⟩

/-- Count tuples that fail the exact expansion inequality for this cut. -/
def permutationBadCountTuples {n : ℕ} (S : Finset (Fin n)) :
    Finset (Fin 3 → Fin (S.card + 1)) :=
  Finset.univ.filter (fun j => 400 * (∑ i, (j i).val) <
    199 * min S.card (n - S.card))

/-- The concrete set of permutation triples failing expansion on a fixed cut. -/
def permutationFixedCutBad {n : ℕ} (S : Finset (Fin n)) :
    Finset (Fin 3 → Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun p => permutationCutFailure p S)

/-- Failure on the physical cut is exactly failure of its outgoing-count
inequality, including the integer strictness. -/
theorem permutationCutFailure_iff_tuple {n : ℕ} (S : Finset (Fin n))
    (p : Fin 3 → Equiv.Perm (Fin n)) :
    permutationCutFailure p S ↔ permutationOutgoingTuple S p ∈ permutationBadCountTuples S := by
  simp only [permutationBadCountTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    permutationOutgoingTuple]
  unfold permutationCutFailure
  rw [permutationFamily_cut_card_sum]
  omega

/-- The failing triples partition exactly by their three outgoing counts. -/
theorem permutationFixedCutBad_card_partition {n : ℕ} (S : Finset (Fin n)) :
    (permutationFixedCutBad S).card = ∑ j ∈ permutationBadCountTuples S,
      (permutationCountTupleEvent S (fun i => (j i).val)).card := by
  classical
  have hmap : ∀ p ∈ permutationFixedCutBad S,
      permutationOutgoingTuple S p ∈ permutationBadCountTuples S := by
    intro p hp
    simp only [permutationFixedCutBad, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact (permutationCutFailure_iff_tuple S p).mp hp
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ext p
  simp only [permutationFixedCutBad, permutationCountTupleEvent, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, heq⟩ i
    exact congrArg (fun f => (f i).val) heq
  · intro hcounts
    have heq : permutationOutgoingTuple S p = j := by
      funext i
      exact Fin.ext (hcounts i)
    refine ⟨?_, heq⟩
    apply (permutationCutFailure_iff_tuple S p).mpr
    rw [heq]
    exact hj

/-- Exact fixed-cut failure count under three independent uniform
permutations, written without division. No entropy inequality is assumed. -/
theorem permutationFixedCutBad_hypergeometric {n : ℕ} (S : Finset (Fin n)) :
    (Nat.choose n S.card)^3 * (permutationFixedCutBad S).card =
      (n.factorial)^3 * ∑ j ∈ permutationBadCountTuples S,
        ∏ i, (Nat.choose S.card (j i).val * Nat.choose (n - S.card) (j i).val) := by
  classical
  rw [permutationFixedCutBad_card_partition, Finset.mul_sum]
  calc
    _ = ∑ j ∈ permutationBadCountTuples S,
        (n.factorial)^3 * ∏ i, (Nat.choose S.card (j i).val * Nat.choose (n - S.card) (j i).val) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact permutationCountTuple_hypergeometric S (fun i => (j i).val)
        (fun i => Nat.le_of_lt_succ (j i).isLt)
    _ = _ := by rw [Finset.mul_sum]

end
end Sude
