import Sude.CutRouting
import Sude.PermutationConditioning

/-! Exact cuts of permutation multigraphs, counted by edge occurrence. -/
namespace Sude
noncomputable section

/-- The labels inside a set whose permutation images leave the set. -/
def permutationOutgoing {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (S : Finset α) : Finset α :=
  S.filter (fun x => p x ∉ S)

/-- The labels outside a set whose permutation images enter the set. -/
def permutationIncoming {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (S : Finset α) : Finset α :=
  Sᶜ.filter (fun x => p x ∈ S)

theorem permutationOutgoing_image {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (S : Finset α) :
    (permutationOutgoing p S).image p = S.image p \ S := by
  ext y
  simp only [Finset.mem_image, permutationOutgoing, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨x, ⟨hx, hout⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hout⟩
  · rintro ⟨⟨x, hx, rfl⟩, hout⟩
    exact ⟨x, ⟨hx, hout⟩, rfl⟩

theorem permutationIncoming_image {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (S : Finset α) :
    (permutationIncoming p S).image p = S \ S.image p := by
  ext y
  simp only [Finset.mem_image, permutationIncoming, Finset.mem_filter, Finset.mem_compl,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨x, ⟨hx, hin⟩, rfl⟩
    refine ⟨hin, ?_⟩
    rintro ⟨v, hv, heq⟩
    exact hx (p.injective heq ▸ hv)
  · rintro ⟨hy, hnot⟩
    refine ⟨p.symm y, ⟨?_, ?_⟩, p.apply_symm_apply y⟩
    · intro hx
      exact hnot ⟨p.symm y, hx, p.apply_symm_apply y⟩
    · simpa using hy

/-- A permutation has as many incoming as outgoing edges across any cut. -/
theorem permutationOutgoing_card_eq_incoming {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (S : Finset α) :
    (permutationOutgoing p S).card = (permutationIncoming p S).card := by
  have hcard : (S.image p).card = S.card := Finset.card_image_of_injective S p.injective
  have hdiff : (S.image p \ S).card = (S \ S.image p).card :=
    Finset.card_sdiff_comm hcard
  rw [← Finset.card_image_of_injective (permutationOutgoing p S) p.injective,
    permutationOutgoing_image, hdiff,
    ← permutationIncoming_image p S, Finset.card_image_of_injective _ p.injective]

/-- A family of permutations acts on labelled edge occurrences by moving the
vertex while preserving the permutation label. -/
def permutationFamilyEdgePerm {r n : ℕ} (p : Fin r → Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin r × Fin n) where
  toFun x := (x.1, p x.1 x.2)
  invFun x := (x.1, (p x.1).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- Each crossing occurrence is either outgoing or incoming; loops do not
cross and parallel edges keep distinct labels. -/
theorem permutationFamily_cut_card {r n : ℕ} (p : Fin r → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    (cutEdges (fun e : Fin r × Fin n => e.2) (fun e => p e.1 e.2) S).card =
      2 * (permutationOutgoing (permutationFamilyEdgePerm p)
        (Finset.univ.filter (fun e : Fin r × Fin n => e.2 ∈ S))).card := by
  let q := permutationFamilyEdgePerm p
  let A : Finset (Fin r × Fin n) := Finset.univ.filter (fun e => e.2 ∈ S)
  have hset : cutEdges (fun e : Fin r × Fin n => e.2) (fun e => p e.1 e.2) S =
      permutationOutgoing q A ∪ permutationIncoming q A := by
    ext e
    simp [cutEdges, permutationOutgoing, permutationIncoming, A, q, permutationFamilyEdgePerm]
  have hdisj : Disjoint (permutationOutgoing q A) (permutationIncoming q A) := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    have ha : e ∈ A := (Finset.mem_filter.mp he).1
    have hb : e ∉ A := Finset.mem_compl.mp (Finset.mem_filter.mp he').1
    exact hb ha
  change (cutEdges (fun e : Fin r × Fin n => e.2) (fun e => p e.1 e.2) S).card =
    2 * (permutationOutgoing q A).card
  rw [hset, Finset.card_union_of_disjoint hdisj, ← permutationOutgoing_card_eq_incoming q A]
  omega

/-- Replacing a cut by its complement preserves all labelled crossing edges. -/
theorem cutEdges_compl_eq {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (S : Finset (Fin n)) :
    cutEdges source target Sᶜ = cutEdges source target S := by
  ext e
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  tauto

/-- The exact integer expansion failure of a labelled permutation triple. -/
def permutationCutFailure {n : ℕ} (p : Fin 3 → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : Prop :=
  200 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card <
    199 * min S.card (n - S.card)

/-- Failure is invariant when the two sides of a cut are exchanged. -/
theorem permutationCutFailure_compl {n : ℕ} (p : Fin 3 → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : permutationCutFailure p Sᶜ ↔ permutationCutFailure p S := by
  unfold permutationCutFailure
  rw [cutEdges_compl_eq]
  simp only [Finset.card_compl, Fintype.card_fin]
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  rw [Nat.sub_sub_self hcard, min_comm]

/-- Every failed cut has a representative on the at-most-half side, with
exactly the same smaller-side cardinality. -/
theorem permutationCutFailure_small_side {n : ℕ} (p : Fin 3 → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (hfail : permutationCutFailure p S) :
    ∃ T : Finset (Fin n), 2 * T.card ≤ n ∧
      T.card = min S.card (n - S.card) ∧ permutationCutFailure p T := by
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  by_cases hsmall : 2 * S.card ≤ n
  · refine ⟨S, hsmall, ?_, hfail⟩
    exact (Nat.min_eq_left (by omega)).symm
  · refine ⟨Sᶜ, ?_, ?_, (permutationCutFailure_compl p S).mpr hfail⟩
    · simp only [Finset.card_compl, Fintype.card_fin]
      omega
    · simp only [Finset.card_compl, Fintype.card_fin]
      exact (Nat.min_eq_right (by omega)).symm

/-- Bad triples with a smaller cut fraction below the source threshold. -/
def permutationSmallCutBad (n : ℕ) : Finset (Fin 3 → Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun p => ∃ S : Finset (Fin n),
    256 * min S.card (n - S.card) < n ∧ permutationCutFailure p S)

/-- Bad triples with a smaller cut fraction at or above the threshold. -/
def permutationLargeCutBad (n : ℕ) : Finset (Fin 3 → Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun p => ∃ S : Finset (Fin n),
    n ≤ 256 * min S.card (n - S.card) ∧ permutationCutFailure p S)

/-- The small-cut event may be counted over subsets of size at most `n/2`,
with the source threshold expressed directly in terms of that size. -/
theorem mem_permutationSmallCutBad_iff {n : ℕ} (p : Fin 3 → Equiv.Perm (Fin n)) :
    p ∈ permutationSmallCutBad n ↔ ∃ S : Finset (Fin n),
      2 * S.card ≤ n ∧ 256 * S.card < n ∧ permutationCutFailure p S := by
  classical
  simp only [permutationSmallCutBad, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨S, hs, hf⟩
    obtain ⟨T, ht, hcard, hfail⟩ := permutationCutFailure_small_side p S hf
    exact ⟨T, ht, by omega, hfail⟩
  · rintro ⟨S, hs, ht, hf⟩
    have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hm : min S.card (n - S.card) = S.card := Nat.min_eq_left (by omega)
    exact ⟨S, by omega, hf⟩

/-- The same reduction applies to the large-cut event, including equality
at the small/large threshold. -/
theorem mem_permutationLargeCutBad_iff {n : ℕ} (p : Fin 3 → Equiv.Perm (Fin n)) :
    p ∈ permutationLargeCutBad n ↔ ∃ S : Finset (Fin n),
      2 * S.card ≤ n ∧ n ≤ 256 * S.card ∧ permutationCutFailure p S := by
  classical
  simp only [permutationLargeCutBad, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨S, hs, hf⟩
    obtain ⟨T, ht, hcard, hfail⟩ := permutationCutFailure_small_side p S hf
    exact ⟨T, ht, by omega, hfail⟩
  · rintro ⟨S, hs, ht, hf⟩
    have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hm : min S.card (n - S.card) = S.card := Nat.min_eq_left (by omega)
    exact ⟨S, by omega, hf⟩

/-- The proved conditioning theorem produces actual derangements satisfying
the exact FC2K routing expansion, provided the two explicit finite failure
sets meet the source's one-in-27 cardinal budget. -/
theorem exists_permutation_expander_of_bad_card {n : ℕ} (hn : 2 ≤ n)
    (hbad : 27 * ((permutationSmallCutBad n).card + (permutationLargeCutBad n).card) <
      Fintype.card (Fin 3 → Equiv.Perm (Fin n))) :
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      ∀ S : Finset (Fin n),
        199 * min S.card (n - S.card) ≤
          200 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card := by
  classical
  obtain ⟨p, hderange, hsmall, hlarge⟩ := exists_derangement_triple_avoiding_two hn
    (permutationSmallCutBad n) (permutationLargeCutBad n) hbad
  refine ⟨p, ?_, ?_⟩
  · intro i v
    exact hderange i v
  · intro S
    by_contra hnot
    have hfail : permutationCutFailure p S := by
      unfold permutationCutFailure
      omega
    by_cases hsize : 256 * min S.card (n - S.card) < n
    · apply hsmall
      simp only [permutationSmallCutBad, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨S, hsize, hfail⟩
    · apply hlarge
      simp only [permutationLargeCutBad, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨S, by omega, hfail⟩

end
end Sude
