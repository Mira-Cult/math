import Sude.CentralWindow

/-! A single first-boundary step for a finite vector of strictly fractional
coordinates. Iteration and the existence of a nonzero kernel direction are
separate obligations. -/
namespace Sude
noncomputable section

/-- Given a nonzero finite direction, a positive common step keeps all active
coordinates in the closed unit interval and puts at least one on its boundary. -/
theorem prefix_first_boundary_move {V : Type*} [Fintype V]
    (x d : V → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hd : ∃ i, d i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ x i + t * d i ∧ x i + t * d i ≤ 1) ∧
      ∃ i, x i + t * d i = 0 ∨ x i + t * d i = 1 := by
  classical
  let T : Finset V := Finset.univ.filter (fun i => d i ≠ 0)
  let radius : V → ℝ := fun i => if 0 < d i then (1 - x i) / d i else x i / (-d i)
  have hT : T.Nonempty := by
    obtain ⟨i, hi⟩ := hd
    exact ⟨i, by simp [T, hi]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image T radius hT
  have hjnz : d j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hradpos : 0 < radius j := by
    dsimp [radius]
    split_ifs with hp
    · exact div_pos (by linarith [(hx j).2]) hp
    · have hn : d j < 0 := lt_of_le_of_ne (le_of_not_gt hp) hjnz
      exact div_pos (hx j).1 (by linarith)
  refine ⟨radius j, hradpos, ?_, ?_⟩
  · intro i
    by_cases hi : d i = 0
    · simp [hi, le_of_lt (hx i).1, le_of_lt (hx i).2]
    · have hiT : i ∈ T := by simp [T, hi]
      have hle := hmin i hiT
      by_cases hp : 0 < d i
      · have hb : radius j * d i ≤ 1 - x i := by
          apply (le_div_iff₀ hp).mp
          simpa [radius, hp] using hle
        have hlo : 0 ≤ radius j * d i := mul_nonneg (le_of_lt hradpos) (le_of_lt hp)
        constructor <;> linarith [(hx i).1]
      · have hn : d i < 0 := lt_of_le_of_ne (le_of_not_gt hp) hi
        have hb : radius j * (-d i) ≤ x i := by
          apply (le_div_iff₀ (by linarith : 0 < -d i)).mp
          simpa [radius, hp] using hle
        have hupper : radius j * d i ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hradpos) (le_of_lt hn)
        constructor <;> nlinarith [(hx i).2]
  · refine ⟨j, ?_⟩
    by_cases hp : 0 < d j
    · right
      have heq : ((1 - x j) / d j) * d j = 1 - x j := div_mul_cancel₀ _ (ne_of_gt hp)
      simp only [radius, if_pos hp]
      linarith
    · left
      have hn : d j < 0 := lt_of_le_of_ne (le_of_not_gt hp) hjnz
      have heq : (x j / (-d j)) * (-d j) = x j := div_mul_cancel₀ _ (by linarith)
      simp only [radius, if_neg hp]
      nlinarith

/-- A common step in a homogeneous direction leaves any fixed linear
constraint unchanged. -/
theorem prefix_common_step_preserves_equation {V : Type*} [Fintype V]
    (x d a : V → ℝ) (t : ℝ) (hkernel : ∑ i, a i * d i = 0) :
    (∑ i, a i * (x i + t * d i)) = ∑ i, a i * x i := by
  calc
    (∑ i, a i * (x i + t * d i)) =
        (∑ i, a i * x i) + t * (∑ i, a i * d i) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i, a i * x i := by rw [hkernel]; ring

end
end Sude
