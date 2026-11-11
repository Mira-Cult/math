import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! A mean and a one-sided window place one indexed target in both supplied
forward reachability intervals. This does not establish the interval bounds,
primality, or any distribution of targets. -/
namespace Sude
noncomputable section

/-- If both supplied intervals cover the part of the window at or above the
mean, some target lies in both intervals. The two starting points are the
actual natural-number diagonal sums and `C` is the common half-width. -/
theorem target_mean_forward_reachable {n : ℕ} (hn : 0 < n)
    (target : Fin n → ℕ) (y D : ℝ) (main anti C : ℕ)
    (hmean : (∑ i, (target i : ℝ)) = (n : ℝ) * y)
    (hwindow : ∀ i, (target i : ℝ) ≤ y + D)
    (hmainLo : (main : ℝ) ≤ y) (hantiLo : (anti : ℝ) ≤ y)
    (hmainHi : y + D ≤ (main : ℝ) + 2 * (C : ℝ))
    (hantiHi : y + D ≤ (anti : ℝ) + 2 * (C : ℝ)) :
    ∃ i, 0 ≤ (target i : ℤ) - (main : ℤ) ∧
      (target i : ℤ) - (main : ℤ) ≤ 2 * (C : ℤ) ∧
      0 ≤ (target i : ℤ) - (anti : ℤ) ∧
      (target i : ℤ) - (anti : ℤ) ≤ 2 * (C : ℤ) := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hsum : (∑ _i : Fin n, y) ≤ ∑ i, (target i : ℝ) := by
    simp [hmean, nsmul_eq_mul]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hnonempty hsum
  have hmlo : (main : ℝ) ≤ (target i : ℝ) := hmainLo.trans hi
  have halo : (anti : ℝ) ≤ (target i : ℝ) := hantiLo.trans hi
  have hmhi : (target i : ℝ) ≤ (main : ℝ) + 2 * (C : ℝ) := (hwindow i).trans hmainHi
  have hahi : (target i : ℝ) ≤ (anti : ℝ) + 2 * (C : ℝ) := (hwindow i).trans hantiHi
  have hmloZ : (main : ℤ) ≤ target i := by exact_mod_cast hmlo
  have haloZ : (anti : ℤ) ≤ target i := by exact_mod_cast halo
  have hmhiZ : (target i : ℤ) ≤ (main : ℤ) + 2 * (C : ℤ) := by exact_mod_cast hmhi
  have hahiZ : (target i : ℤ) ≤ (anti : ℤ) + 2 * (C : ℤ) := by exact_mod_cast hahi
  exact ⟨i, by omega, by omega, by omega, by omega⟩

end
end Sude
