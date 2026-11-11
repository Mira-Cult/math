import Sude.PrefixOneLevelRounding

/-! Converting a binary rounding vector into actual labelled slot selections. -/
namespace Sude
noncomputable section

/-- A binary vector with prescribed integral group sums selects exactly the
specified number of labelled slots in every occupied group. -/
theorem prefix_binary_vector_to_selection {S G : Type*} [DecidableEq S] [DecidableEq G]
    (U : Finset S) (group : S → G) (m : G → ℕ) (y : S → ℝ)
    (hy : ∀ s ∈ U, y s = 0 ∨ y s = 1)
    (hgroup : ∀ g ∈ U.image group,
      (∑ s ∈ U, if group s = g then y s else 0) = (m g : ℝ)) :
    ∃ T : Finset S, T ⊆ U ∧
      (∀ s ∈ U, y s = if s ∈ T then 1 else 0) ∧
      (∀ g ∈ U.image group, (T.filter (fun s => group s = g)).card = m g) := by
  classical
  let T := U.filter (fun s => y s = 1)
  have hT : T ⊆ U := Finset.filter_subset _ _
  have hyT : ∀ s ∈ U, y s = if s ∈ T then 1 else 0 := by
    intro s hs
    rcases hy s hs with hzero | hone
    · have hnot : s ∉ T := by simp [T, hzero]
      simp [hzero, hnot]
    · have hin : s ∈ T := Finset.mem_filter.mpr ⟨hs, hone⟩
      simp [hone, hin]
  refine ⟨T, hT, hyT, ?_⟩
  intro g hg
  have heq : (∑ s ∈ U, if group s = g then y s else 0) =
      ((T.filter (fun s => group s = g)).card : ℝ) := by
    calc
      _ = ∑ s ∈ U, if group s = g ∧ s ∈ T then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hyT s hs]
        split_ifs <;> simp_all
      _ = _ := by
        have hf : U.filter (fun s => group s = g ∧ s ∈ T) =
            T.filter (fun s => group s = g) := by
          ext s
          simp [T, and_comm, and_left_comm]
        simp only [← Finset.sum_filter, hf, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hh := hgroup g hg
  rw [heq] at hh
  exact_mod_cast hh

end
end Sude
