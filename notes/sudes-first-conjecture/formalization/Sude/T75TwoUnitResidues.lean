import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

/-! The two-free-coordinate modular step for T75's finite favorable gaps.
This does not produce prime targets or prove an arbitrary-modulus theorem. -/
namespace Sude

/-- The favorable even gaps in T75.5. -/
def t75FavorableGaps : Finset ℕ :=
  {2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 36, 42}

/-- Every even residue modulo a T75 favorable gap is the sum of two
reduced residues. Both witnesses use canonical representatives in `[0,h)`.
The entire displayed finite domain is kernel checked. -/
theorem t75_favorable_two_unit_residues :
    ∀ h ∈ t75FavorableGaps, ∀ c ∈ Finset.range h, c % 2 = 0 →
      ∃ a ∈ Finset.range h, ∃ b ∈ Finset.range h,
        Nat.Coprime a h ∧ Nat.Coprime b h ∧ (a + b) % h = c := by
  decide +kernel

end Sude
