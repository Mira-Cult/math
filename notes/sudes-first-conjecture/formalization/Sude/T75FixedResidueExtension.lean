import Sude.T75TwoUnitResidues

/-! Extend an arbitrary supplied reduced-residue list by two reduced residues
at the selected T75 favorable gap. No primes or targets are constructed. -/
namespace Sude

/-- If the desired canonical residue has the same parity as the sum of the
already-fixed list, two further reduced residues achieve it modulo the
favorable gap. The original list is preserved as a literal prefix. -/
theorem t75_extend_fixed_unit_residues {h c : ℕ} (xs : List ℕ)
    (hh : h ∈ t75FavorableGaps) (hc : c < h)
    (hfixed : ∀ x ∈ xs, x < h ∧ Nat.Coprime x h)
    (hparity : c % 2 = xs.sum % 2) :
    ∃ a b : ℕ,
      a < h ∧ Nat.Coprime a h ∧ b < h ∧ Nat.Coprime b h ∧
      (xs ++ [a, b]).length = xs.length + 2 ∧
      (∀ x ∈ xs ++ [a, b], x < h ∧ Nat.Coprime x h) ∧
      (xs ++ [a, b]).sum % h = c := by
  have hcases : h = 2 ∨ h = 4 ∨ h = 6 ∨ h = 8 ∨ h = 10 ∨ h = 12 ∨
      h = 14 ∨ h = 16 ∨ h = 18 ∨ h = 20 ∨ h = 22 ∨ h = 24 ∨ h = 26 ∨
      h = 28 ∨ h = 30 ∨ h = 36 ∨ h = 42 := by
    simpa [t75FavorableGaps] using hh
  have hp : 0 < h := by
    rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  let d := (c + h - xs.sum % h) % h
  have hdlt : d < h := Nat.mod_lt _ hp
  have hdeven : d % 2 = 0 := by
    dsimp [d]
    rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  obtain ⟨a, ha, b, hb, hca, hcb, hab⟩ :=
    t75_favorable_two_unit_residues h hh d (Finset.mem_range.mpr hdlt) hdeven
  have hsum : (xs.sum + (a + b)) % h = c := by
    dsimp [d] at hab
    rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  refine ⟨a, b, Finset.mem_range.mp ha, hca, Finset.mem_range.mp hb, hcb, ?_, ?_, ?_⟩
  · simp
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · exact hfixed x hx
    · exact ⟨Finset.mem_range.mp ha, hca⟩
    · exact ⟨Finset.mem_range.mp hb, hcb⟩
  · simpa [List.sum_append, add_assoc] using hsum

end Sude
