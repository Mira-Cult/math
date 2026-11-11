import Sude.TargetRouting

/-! A prime already present in a supplied target vector can serve as both
independent diagonal targets. Reachability by physical rectangle grids is a
separate hypothesis. -/
namespace Sude
noncomputable section

/-- For odd order, both actual diagonal sums are odd. -/
theorem mainSum_odd_of_odd_order {n : ℕ} (hn : Odd n)
    (a : Cell n ≃ Fin (n*n)) : Odd (mainSum a) := by
  apply odd_sum_of_odd_entries hn
  intro i
  exact oddPrime_odd _

theorem antiSum_odd_of_odd_order {n : ℕ} (hn : Odd n)
    (a : Cell n ≃ Fin (n*n)) : Odd (antiSum a) := by
  apply odd_sum_of_odd_entries hn
  intro i
  exact oddPrime_odd _

/-- A nonempty supplied odd-prime target vector supplies one common prime
for both diagonals. The signed differences are even and lie in the displayed
triangle budget. This does not assert that a physical grid reaches them. -/
theorem diagonal_prime_target_from_vector {n : ℕ} (hn : Odd n)
    (a : Cell n ≃ Fin (n*n)) (f : Fin n → ℕ) (y U D : ℝ)
    (hf : ∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D)
    (hm : |(mainSum a : ℝ) - y| ≤ U)
    (ha : |(antiSum a : ℝ) - y| ≤ U) :
    ∃ q : ℕ, Nat.Prime q ∧ Odd q ∧ |(q : ℝ) - y| ≤ D ∧
      2 * halfLineDemand q (mainSum a) = (q : ℤ) - mainSum a ∧
      2 * halfLineDemand q (antiSum a) = (q : ℤ) - antiSum a ∧
      |(q : ℝ) - (mainSum a : ℝ)| ≤ U + D ∧
      |(q : ℝ) - (antiSum a : ℝ)| ≤ U + D := by
  have hpos : 0 < n := by
    obtain ⟨k, hk⟩ := hn
    omega
  let i : Fin n := ⟨0, hpos⟩
  obtain ⟨hp, ho, hrad⟩ := hf i
  refine ⟨f i, hp, ho, hrad,
    halfLineDemand_exact _ _ ho (mainSum_odd_of_odd_order hn a),
    halfLineDemand_exact _ _ ho (antiSum_odd_of_odd_order hn a), ?_, ?_⟩
  · have h := abs_add_le ((f i : ℝ) - y) (y - (mainSum a : ℝ))
    have hy : |y - (mainSum a : ℝ)| ≤ U := by simpa only [abs_sub_comm] using hm
    have heq : (f i : ℝ) - (mainSum a : ℝ) =
        ((f i : ℝ) - y) + (y - (mainSum a : ℝ)) := by ring
    rw [heq]
    linarith
  · have h := abs_add_le ((f i : ℝ) - y) (y - (antiSum a : ℝ))
    have hy : |y - (antiSum a : ℝ)| ≤ U := by simpa only [abs_sub_comm] using ha
    have heq : (f i : ℝ) - (antiSum a : ℝ) =
        ((f i : ℝ) - y) + (y - (antiSum a : ℝ)) := by ring
    rw [heq]
    linarith

end
end Sude
