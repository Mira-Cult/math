import Sude.EvenGrid

/-! Centering a complete even subset-sum grid. This is a capacity lemma;
it does not supply graph flows or prime-pair populations. -/
namespace Sude
noncomputable section

/-- Exact total of the binary prefix, including the zero-stage case. -/
theorem binary_gap_total (P : ℕ) :
    (∑ k ∈ Finset.range P, 2 ^ (k + 1)) = 2 ^ (P + 1) - 2 := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_range_succ, ih]
    have hpos : 0 < 2 ^ (P + 1) := Nat.two_pow_pos _
    rw [show P + 1 + 1 = (P + 1) + 1 by omega, pow_succ]
    omega

/-- The even grid point immediately below the real midpoint. -/
def evenGridCenter (R : ℕ) : ℕ := 2 * (R / 4)

theorem evenGridCenter_twice_le (R : ℕ) : 2 * evenGridCenter R ≤ R := by
  dsimp [evenGridCenter]
  omega

theorem evenGridCenter_even (R : ℕ) : 2 ∣ evenGridCenter R := by
  exact ⟨R / 4, rfl⟩

/-- For an even total, the chosen even grid point is within one unit of
its real midpoint; the doubled error is at most two. -/
theorem evenGridCenter_midpoint_error (R : ℕ) (heven : 2 ∣ R) :
    2 * evenGridCenter R ≤ R ∧ R - 2 * evenGridCenter R ≤ 2 := by
  obtain ⟨m, hm⟩ := heven
  dsimp [evenGridCenter]
  omega

/-- Every even signed transfer bounded by the lower midpoint is represented
by a physical subset sum relative to that midpoint. -/
theorem centered_even_grid {α : Type*} [DecidableEq α] (S : Finset α)
    (gap : α → ℕ) (R : ℕ) (hgrid : CompleteEvenGrid S gap R)
    (t : ℤ) (heven : (2 : ℤ) ∣ t)
    (hlower : -(evenGridCenter R : ℤ) ≤ t) (hupper : t ≤ evenGridCenter R) :
    ∃ T : Finset α, T ⊆ S ∧
      ((∑ k ∈ T, gap k : ℕ) : ℤ) - evenGridCenter R = t := by
  have hc : 2 * evenGridCenter R ≤ R := evenGridCenter_twice_le R
  have hnonneg : 0 ≤ (evenGridCenter R : ℤ) + t := by omega
  let q := Int.toNat ((evenGridCenter R : ℤ) + t)
  have hq : (q : ℤ) = (evenGridCenter R : ℤ) + t := Int.toNat_of_nonneg hnonneg
  have hqR : q ≤ R := by omega
  have hqEvenZ : (2 : ℤ) ∣ (q : ℤ) := by
    rcases heven with ⟨m, hm⟩
    refine ⟨(R / 4 : ℕ) + m, ?_⟩
    dsimp [evenGridCenter] at hq
    omega
  have hqEven : 2 ∣ q := by exact_mod_cast hqEvenZ
  obtain ⟨T, hT, hsum⟩ := hgrid q hqR hqEven
  refine ⟨T, hT, ?_⟩
  exact_mod_cast (show ((∑ k ∈ T, gap k : ℕ) : ℤ) - evenGridCenter R = t by
    rw [hsum, hq]
    omega)

end
end Sude
