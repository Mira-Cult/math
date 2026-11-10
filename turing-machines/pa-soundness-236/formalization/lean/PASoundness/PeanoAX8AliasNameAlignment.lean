import PASoundness.PeanoAX8NameAlignment

/-! Alias-case finite name alignment. This does not assert an AX8 instance. -/
namespace PASoundness.PeanoAX8AliasNameAlignment
open PeanoFreeNamePermutation PeanoAX8NameAlignment

/-- When only b and c are distinct, reserve canonical input name 4 by
choosing a dummy source name outside the finite support. The supported names
other than b,c are all moved above the canonical low block. -/
theorem exists_alias_alignment (support : Finset Nat) (b c : Nat) (hbc : b ≠ c) :
    ∃ xs : List (Nat × Nat),
      applyName xs b = 5 ∧ applyName xs c = 3 ∧
      (∀ n ∈ support, n ≠ b → n ≠ c → 6 ≤ applyName xs n) ∧
      (∀ n ∈ support, applyName xs n ≠ 4) := by
  let dummy := max (max b c) (support.sup id) + 1
  have hdb : dummy ≠ b := by dsimp [dummy]; omega
  have hdc : dummy ≠ c := by dsimp [dummy]; omega
  have hfresh : ∀ n ∈ support, n ≠ dummy := by
    intro n hn h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) hn
    dsimp [dummy] at h
    omega
  obtain ⟨xs, _ha, hb, hc, hrest⟩ := exists_alignment support dummy b c hdb hdc hbc
  refine ⟨xs, hb, hc, ?_, ?_⟩
  · intro n hn hnb hnc
    exact hrest n hn (hfresh n hn) hnb hnc
  · intro n hn
    by_cases hnb : n = b
    · subst n; simp [hb]
    by_cases hnc : n = c
    · subst n; simp [hc]
    have hhigh := hrest n hn (hfresh n hn) hnb hnc
    omega

end PASoundness.PeanoAX8AliasNameAlignment

#print axioms PASoundness.PeanoAX8AliasNameAlignment.exists_alias_alignment
