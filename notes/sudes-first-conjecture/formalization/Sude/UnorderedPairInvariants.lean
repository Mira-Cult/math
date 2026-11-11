import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic

/-! Algebraic consequences of identity-or-reversal endpoint preservation.
This does not establish any physical switch or later flow property. -/
namespace Sude

/-- Unchanged or reversed natural endpoints preserve their sum and the
absolute value of their signed integer difference. -/
theorem unordered_pair_sum_and_signed_gap (a₀ a₁ b₀ b₁ : ℕ)
    (h : (b₀ = a₀ ∧ b₁ = a₁) ∨ (b₀ = a₁ ∧ b₁ = a₀)) :
    b₀ + b₁ = a₀ + a₁ ∧
      |(b₁ : ℤ) - (b₀ : ℤ)| = |(a₁ : ℤ) - (a₀ : ℤ)| := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp
  · simp [Nat.add_comm, abs_sub_comm]

/-- In particular, if the original high endpoint exceeds the low endpoint
by g, the new signed integer gap has absolute value exactly g, regardless of
whether the endpoints were reversed. -/
theorem unordered_pair_gap_magnitude (a₀ a₁ b₀ b₁ g : ℕ)
    (h : (b₀ = a₀ ∧ b₁ = a₁) ∨ (b₀ = a₁ ∧ b₁ = a₀))
    (hgap : a₁ = a₀ + g) :
    |(b₁ : ℤ) - (b₀ : ℤ)| = (g : ℤ) := by
  rw [(unordered_pair_sum_and_signed_gap a₀ a₁ b₀ b₁ h).2, hgap]
  simp

end Sude
