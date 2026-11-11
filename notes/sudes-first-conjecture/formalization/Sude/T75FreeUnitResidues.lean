import Sude.T75TwoUnitResidues

/-! A bounded modular lift for any number of free coordinates, using T75's
finite favorable gaps. It does not assert prime or target existence. -/
namespace Sude

/-- For a favorable gap, any canonical residue with the parity of the number
of coordinates is a sum of that many reduced residues. Repetition is allowed. -/
theorem t75_free_unit_residues {h m c : ℕ}
    (hh : h ∈ t75FavorableGaps) (hm : 2 ≤ m) (hc : c < h)
    (hparity : c % 2 = m % 2) :
    ∃ xs : List ℕ, xs.length = m ∧
      (∀ x ∈ xs, x < h ∧ Nat.Coprime x h) ∧ xs.sum % h = c := by
  have hcases : h = 2 ∨ h = 4 ∨ h = 6 ∨ h = 8 ∨ h = 10 ∨ h = 12 ∨
      h = 14 ∨ h = 16 ∨ h = 18 ∨ h = 20 ∨ h = 22 ∨ h = 24 ∨ h = 26 ∨
      h = 28 ∨ h = 30 ∨ h = 36 ∨ h = 42 := by
    simpa [t75FavorableGaps] using hh
  have hp : 0 < h := by rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  let d := (c + h - ((m - 2) % h)) % h
  have hdlt : d < h := Nat.mod_lt _ hp
  have hdeven : d % 2 = 0 := by
    dsimp [d]
    rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  obtain ⟨a, ha, b, hb, hca, hcb, hab⟩ :=
    t75_favorable_two_unit_residues h hh d (Finset.mem_range.mpr hdlt) hdeven
  have hsum : ((m - 2) + (a + b)) % h = c := by
    dsimp [d] at hab
    rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  refine ⟨List.replicate (m - 2) 1 ++ [a, b], ?_, ?_, ?_⟩
  · simp; omega
  · intro x hx
    simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with ⟨_, rfl⟩ | rfl | rfl
    · exact ⟨by omega, Nat.coprime_one_left h⟩
    · exact ⟨Finset.mem_range.mp ha, hca⟩
    · exact ⟨Finset.mem_range.mp hb, hcb⟩
  · simpa [List.sum_append, List.sum_replicate, add_assoc] using hsum

end Sude
