import PASoundness.PeanoAX8NameAlignment
import PASoundness.PeanoAX8AliasNameAlignment
import PASoundness.PeanoAX8DecodedFresh
import PASoundness.PeanoAX8PermutationFreshness

/-! Formula-level freshness after finite AX8 name standardization. This does
not establish the syntactic binder alignment or an AX8 derivation. -/
namespace PASoundness.PeanoAX8RenamedFresh
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoFreeNamePermutation

/-- For three pairwise distinct names with c fresh in φ, standardization
maps a,b,c to 4,5,3 and makes 0,1,2,3 fresh in the renamed formula. -/
theorem distinct_fresh (φ : Peano.Formula) (a b c : Nat)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hc : c ∉ φ.freeVarFinset) :
    ∃ xs : List (Nat × Nat),
      applyName xs a = 4 ∧ applyName xs b = 5 ∧ applyName xs c = 3 ∧
      ∀ k, k < 4 → k ∉ (applyFormula xs φ).freeVarFinset := by
  obtain ⟨xs, ha, hb, hc', hother⟩ :=
    PeanoAX8NameAlignment.exists_alignment φ.freeVarFinset a b c hab hac hbc
  refine ⟨xs, ha, hb, hc', ?_⟩
  intro k hk
  exact PeanoAX8PermutationFreshness.fresh_below_four xs φ a b c ha hb hc hother k hk

/-- In the alias case the same construction leaves canonical input name 4
fresh as well, so it can be safely specialized to zero. -/
theorem alias_fresh (φ : Peano.Formula) (b c : Nat)
    (hbc : b ≠ c) (hc : c ∉ φ.freeVarFinset) :
    ∃ xs : List (Nat × Nat),
      applyName xs b = 5 ∧ applyName xs c = 3 ∧
      ∀ k, k < 5 → k ∉ (applyFormula xs φ).freeVarFinset := by
  obtain ⟨xs, hb, hc', hother, _hfour⟩ :=
    PeanoAX8AliasNameAlignment.exists_alias_alignment φ.freeVarFinset b c hbc
  refine ⟨xs, hb, hc', ?_⟩
  intro k hk
  apply PeanoFreeNameFreshness.permuted_fresh
  intro n hn
  by_cases hnb : n = b
  · subst n; rw [hb]; omega
  have hnc : n ≠ c := by intro h; subst n; exact hc hn
  have hhigh := hother n hn hnb hnc
  omega

end PASoundness.PeanoAX8RenamedFresh

#print axioms PASoundness.PeanoAX8RenamedFresh.distinct_fresh
#print axioms PASoundness.PeanoAX8RenamedFresh.alias_fresh
