import Sude.CentralWindow

/-! The fractional part of an integral group sum remains integral, since all
other unit-box coordinates are zero or one. -/
namespace Sude
noncomputable section

/-- If the full group sum is integral, the sum over its strictly fractional
coordinates is integral too. -/
theorem prefix_fractional_group_sum_integral {S : Type*} (B : Finset S)
    (x : S → ℝ) (hx : ∀ s ∈ B, 0 ≤ x s ∧ x s ≤ 1)
    (hint : ∃ z : ℤ, (∑ s ∈ B, x s) = (z : ℝ)) :
    ∃ z : ℤ, (∑ s ∈ B.filter (fun s => 0 < x s ∧ x s < 1), x s) = (z : ℝ) := by
  classical
  let F := B.filter (fun s => 0 < x s ∧ x s < 1)
  let I := B \ F
  have hFI : F ⊆ B := Finset.filter_subset _ _
  have hI : ∀ s ∈ I, x s = 0 ∨ x s = 1 := by
    intro s hs
    have hB : s ∈ B := (Finset.mem_sdiff.mp hs).1
    have hnot : ¬(0 < x s ∧ x s < 1) := by
      have hnot' := (Finset.mem_sdiff.mp hs).2
      simpa [F, hB] using hnot'
    obtain ⟨h0, h1⟩ := hx s hB
    rcases lt_or_eq_of_le h0 with hlo | hlo
    · by_cases hlt : x s < 1
      · exact False.elim (hnot ⟨hlo, hlt⟩)
      · right; linarith
    · left; linarith
  let zI : ℤ := ∑ s ∈ I, if x s = 1 then 1 else 0
  have hIint : (∑ s ∈ I, x s) = (zI : ℝ) := by
    dsimp [zI]
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rcases hI s hs with hzero | hone
    · simp [hzero]
    · simp [hone]
  obtain ⟨z, hz⟩ := hint
  have hsplit : (∑ s ∈ F, x s) + ∑ s ∈ I, x s = ∑ s ∈ B, x s := by
    dsimp [I]
    simpa [add_comm] using Finset.sum_sdiff (f := x) hFI
  refine ⟨z - zI, ?_⟩
  change (∑ s ∈ F, x s) = ((z - zI : ℤ) : ℝ)
  rw [Int.cast_sub]
  linarith

end
end Sude
