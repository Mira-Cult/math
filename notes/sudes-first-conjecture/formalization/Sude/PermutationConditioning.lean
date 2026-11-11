import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Tactic

/-! The source's conditioning step on three uniformly chosen permutations. -/
namespace Sude

/-- At least one third of all permutations are derangements, for every
finite order at least two. This uses mathlib's exact derangement recurrence. -/
theorem factorial_le_three_numDerangements {n : ℕ} (hn : 2 ≤ n) :
    n.factorial ≤ 3 * numDerangements n := by
  have h : ∀ k : ℕ, (k + 2).factorial ≤ 3 * numDerangements (k + 2) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more k hk hk1 =>
      have hk1' : (k + 3).factorial ≤ 3 * numDerangements (k + 3) := by
        simpa [Nat.add_assoc] using hk1
      have hsum : (k + 2).factorial + (k + 3).factorial ≤
          3 * (numDerangements (k + 2) + numDerangements (k + 3)) := by omega
      have hmul := Nat.mul_le_mul_left (k + 3) hsum
      rw [show k + 2 + 2 = (k + 2) + 2 by omega, numDerangements_add_two]
      rw [Nat.factorial_succ, Nat.factorial_succ]
      have hfact : (k + 3).factorial = (k + 3) * (k + 2).factorial := by
        simpa [Nat.add_assoc] using Nat.factorial_succ (k + 2)
      rw [hfact] at hmul
      nlinarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using h k

/-- Exact card form of the one-third bound for actual permutations. -/
theorem card_perm_le_three_derangements {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (Equiv.Perm (Fin n)) ≤ 3 * Fintype.card (derangements (Fin n)) := by
  rw [Fintype.card_perm, Fintype.card_fin, card_derangements_fin_eq_numDerangements]
  exact factorial_le_three_numDerangements hn

/-- Three independent uniformly sampled permutations have at least a
one-in-27 proportion of all triples with no fixed points. -/
theorem card_triples_le_27_derangements {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (Fin 3 → Equiv.Perm (Fin n)) ≤
      27 * Fintype.card (Fin 3 → derangements (Fin n)) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  have h := Nat.pow_le_pow_left (card_perm_le_three_derangements hn) 3
  simpa [mul_pow] using h

/-- A bad-event set smaller than one twenty-seventh of all triples cannot
cover the triples of derangements. This is the finite conditioning step;
the cut-event cardinal bound remains a separate obligation. -/
theorem exists_derangement_triple_avoiding {n : ℕ} (hn : 2 ≤ n)
    (bad : Finset (Fin 3 → Equiv.Perm (Fin n)))
    (hbad : 27 * bad.card < Fintype.card (Fin 3 → Equiv.Perm (Fin n))) :
    ∃ f : Fin 3 → Equiv.Perm (Fin n),
      (∀ i, f i ∈ derangements (Fin n)) ∧ f ∉ bad := by
  classical
  let good : Finset (Fin 3 → Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun f => ∀ i, f i ∈ derangements (Fin n))
  have hcard : good.card = Fintype.card (Fin 3 → derangements (Fin n)) := by
    change (Finset.univ.filter (fun f : Fin 3 → Equiv.Perm (Fin n) =>
      ∀ i, f i ∈ derangements (Fin n))).card = _
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr Equiv.subtypePiEquivPi
  have hlt : bad.card < good.card := by
    have hbound := card_triples_le_27_derangements hn
    rw [← hcard] at hbound
    omega
  have hnot : ¬ good ⊆ bad := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨f, hf, hnotbad⟩ := Finset.not_subset.mp hnot
  exact ⟨f, (Finset.mem_filter.mp hf).2, hnotbad⟩

/-- Small-cut and large-cut failures may overlap. Their cardinalities can be
added conservatively before selecting a triple of derangements. -/
theorem exists_derangement_triple_avoiding_two {n : ℕ} (hn : 2 ≤ n)
    (small large : Finset (Fin 3 → Equiv.Perm (Fin n)))
    (hbad : 27 * (small.card + large.card) <
      Fintype.card (Fin 3 → Equiv.Perm (Fin n))) :
    ∃ f : Fin 3 → Equiv.Perm (Fin n),
      (∀ i, f i ∈ derangements (Fin n)) ∧ f ∉ small ∧ f ∉ large := by
  classical
  have hcard := Finset.card_union_le small large
  have hunion : 27 * (small ∪ large).card <
      Fintype.card (Fin 3 → Equiv.Perm (Fin n)) := by omega
  obtain ⟨f, hf, havoid⟩ := exists_derangement_triple_avoiding hn (small ∪ large) hunion
  simp only [Finset.mem_union, not_or] at havoid
  exact ⟨f, hf, havoid.1, havoid.2⟩

end Sude
