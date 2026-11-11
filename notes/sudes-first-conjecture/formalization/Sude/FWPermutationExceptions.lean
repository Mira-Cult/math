import Sude.PermutationExceptions

/-! FW's exact cut-failure event and its finite exception-pattern cover.
These combinatorial facts alone do not establish an expander or any
analytic probability estimate. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- Strict failure of FW6's `519/500` labelled cut expansion. -/
def fwPermutationCutFailure {n : ℕ} (p : Fin 3 → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : Prop :=
  500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card <
    519 * min S.card (n - S.card)

/-- Complementing a cut preserves the FW failure event. -/
theorem fwPermutationCutFailure_compl {n : ℕ} (p : Fin 3 → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : fwPermutationCutFailure p Sᶜ ↔ fwPermutationCutFailure p S := by
  unfold fwPermutationCutFailure
  rw [cutEdges_compl_eq]
  simp only [Finset.card_compl, Fintype.card_fin]
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  rw [Nat.sub_sub_self hcard, min_comm]

/-- FW's bad outgoing-count tuples, including the strict integer threshold. -/
def fwPermutationBadCountTuples {n : ℕ} (S : Finset (Fin n)) :
    Finset (Fin 3 → Fin (S.card + 1)) :=
  Finset.univ.filter (fun j => 1000 * (∑ i, (j i).val) <
    519 * min S.card (n - S.card))

/-- The physical cut fails exactly when its outgoing tuple meets FW's
threshold; every labelled crossing occurrence is counted. -/
theorem fwPermutationCutFailure_iff_tuple {n : ℕ} (S : Finset (Fin n))
    (p : Fin 3 → Equiv.Perm (Fin n)) :
    fwPermutationCutFailure p S ↔
      permutationOutgoingTuple S p ∈ fwPermutationBadCountTuples S := by
  simp only [fwPermutationBadCountTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    permutationOutgoingTuple]
  unfold fwPermutationCutFailure
  rw [permutationFamily_cut_card_sum]
  omega

/-- The FW failure event for a fixed cut in the uniform triple sample. -/
def fwPermutationFixedCutBad {n : ℕ} (S : Finset (Fin n)) :
    Finset (Fin 3 → Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun p => fwPermutationCutFailure p S)

/-- Partition the exact FW fixed-cut event by its outgoing-count tuple. -/
theorem fwPermutationFixedCutBad_card_partition {n : ℕ} (S : Finset (Fin n)) :
    (fwPermutationFixedCutBad S).card = ∑ j ∈ fwPermutationBadCountTuples S,
      (permutationCountTupleEvent S (fun i => (j i).val)).card := by
  classical
  have hmap : ∀ p ∈ fwPermutationFixedCutBad S,
      permutationOutgoingTuple S p ∈ fwPermutationBadCountTuples S := by
    intro p hp
    simp only [fwPermutationFixedCutBad, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact (fwPermutationCutFailure_iff_tuple S p).mp hp
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ext p
  simp only [fwPermutationFixedCutBad, permutationCountTupleEvent, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, heq⟩ i
    exact congrArg (fun f => (f i).val) heq
  · intro hcounts
    have heq : permutationOutgoingTuple S p = j := by
      funext i
      exact Fin.ext (hcounts i)
    refine ⟨?_, heq⟩
    apply (fwPermutationCutFailure_iff_tuple S p).mpr
    rw [heq]
    exact hj

/-- Each FW failure has an actual outgoing exception set of at most
`⌊519|S|/1000⌋`; all other labelled inputs map back into the cut. -/
theorem fwPermutationFixedCutBad_subset_exception_union {n : ℕ} (S : Finset (Fin n)) :
    fwPermutationFixedCutBad S ⊆
      (permutationExceptionPatterns S (519 * S.card / 1000)).biUnion
        (fun E => permutationFamilyContainmentEvent (permutationKeptInputs S E) S) := by
  classical
  intro p hp
  let E := permutationOutgoing (permutationFamilyEdgePerm p) (permutationCutPositions S)
  have hfail : fwPermutationCutFailure p S := (Finset.mem_filter.mp hp).2
  have hout : 1000 * E.card < 519 * S.card := by
    have hcut := permutationFamily_cut_card p S
    have hE : E = permutationOutgoing (permutationFamilyEdgePerm p)
        (Finset.univ.filter (fun e : Fin 3 × Fin n => e.2 ∈ S)) := by
      dsimp [E]
      congr 1
      ext e
      change e ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ S) ↔
        e ∈ Finset.univ.filter (fun x : Fin 3 × Fin n => x.2 ∈ S)
      simp
    rw [← hE] at hcut
    unfold fwPermutationCutFailure at hfail
    rw [hcut] at hfail
    have hmin : min S.card (n - S.card) ≤ S.card := Nat.min_le_left _ _
    omega
  have hEpat : E ∈ permutationExceptionPatterns S (519 * S.card / 1000) := by
    simp only [permutationExceptionPatterns, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨permutationOutgoing_cutPositions_subset S p, by omega⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨E, hEpat, permutation_actual_exceptions_contained S p⟩

/-- Finite union bound, with no independence between exception events. -/
theorem fwPermutationFixedCutBad_exception_union_bound {n : ℕ} (S : Finset (Fin n)) :
    (fwPermutationFixedCutBad S).card ≤
      ∑ E ∈ permutationExceptionPatterns S (519 * S.card / 1000),
        (permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card := by
  exact (Finset.card_le_card (fwPermutationFixedCutBad_subset_exception_union S)).trans
    Finset.card_biUnion_le

end
end Sude
