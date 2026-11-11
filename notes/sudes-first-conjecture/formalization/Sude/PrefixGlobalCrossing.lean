import Sude.CentralWindow

/-! A global bounded-jump crossing for finite independent stage paths.
Only one stage advances at a time, so the error has no stage-count factor. -/
namespace Sude
noncomputable section

/-- A product of finite stage paths contains a state within `C/2` of any
bracketed target, provided every single-stage forward jump is at most `C`.
Neither monotonicity nor distinct numerical values is required. -/
theorem prefix_global_path_near {J : Type*} [Fintype J] [DecidableEq J]
    (m : J → ℕ) (w : ∀ j, Fin (m j + 1) → ℝ) (target C : ℝ)
    (hC : 0 ≤ C)
    (hleft : (∑ j, w j ⟨0, by omega⟩) ≤ target)
    (hright : target ≤ ∑ j, w j ⟨m j, by omega⟩)
    (hjump : ∀ j (i : Fin (m j + 1)) (hi : i.val < m j),
      w j ⟨i.val + 1, by omega⟩ - w j i ≤ C) :
    ∃ p : ∀ j, Fin (m j + 1), |(∑ j, w j (p j)) - target| ≤ C / 2 := by
  classical
  let S : Finset (∀ j, Fin (m j + 1)) := Finset.univ.filter (fun p => (∑ j, w j (p j)) ≤ target)
  let rank : (∀ j, Fin (m j + 1)) → ℕ := fun p => ∑ j, (p j).val
  have hne : S.Nonempty := by
    refine ⟨fun j => ⟨0, by omega⟩, ?_⟩
    simpa [S] using hleft
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S rank hne
  have hpval : (∑ j, w j (p j)) ≤ target := (Finset.mem_filter.mp hp).2
  by_cases hclose : target - (∑ j, w j (p j)) ≤ C / 2
  · refine ⟨p, ?_⟩
    rw [abs_le]
    constructor <;> linarith
  · have hnfinal : ¬ ∀ j, (p j).val = m j := by
      intro hfinal
      have heq : (∑ j, w j (p j)) = ∑ j, w j ⟨m j, by omega⟩ := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        exact Fin.ext (hfinal j)
      linarith
    push_neg at hnfinal
    obtain ⟨j, hj⟩ := hnfinal
    have hjlt : (p j).val < m j := by have := (p j).isLt; omega
    let q : ∀ j, Fin (m j + 1) := Function.update p j ⟨(p j).val + 1, by omega⟩
    have hqrank : rank q = rank p + 1 := by
      have hf : (fun i => (q i).val) = Function.update (fun i => (p i).val) j ((p j).val + 1) := by
        funext i
        by_cases hi : i = j
        · subst i; simp [q]
        · simp [q, hi]
      unfold rank
      rw [hf, Finset.sum_update_of_mem (Finset.mem_univ j)]
      simp only [Finset.sdiff_singleton_eq_erase]
      have hb := Finset.add_sum_erase Finset.univ (fun i => (p i).val) (Finset.mem_univ j)
      omega
    have hqgt : target < ∑ j, w j (q j) := by
      by_contra h
      have hqS : q ∈ S := by simpa [S] using le_of_not_gt h
      have := hmax q hqS
      omega
    have hstep : (∑ i, w i (q i)) - (∑ i, w i (p i)) ≤ C := by
      have heq : (∑ i, w i (q i)) - (∑ i, w i (p i)) =
          w j ⟨(p j).val + 1, by omega⟩ - w j (p j) := by
        have hf : (fun i => w i (q i)) = Function.update (fun i => w i (p i)) j
            (w j ⟨(p j).val + 1, by omega⟩) := by
          funext i
          by_cases hi : i = j
          · subst i; simp [q]
          · simp [q, hi]
        rw [hf, Finset.sum_update_of_mem (Finset.mem_univ j)]
        simp only [Finset.sdiff_singleton_eq_erase]
        have hb := Finset.add_sum_erase Finset.univ (fun i => w i (p i)) (Finset.mem_univ j)
        linarith
      rw [heq]
      exact hjump j (p j) hjlt
    refine ⟨q, ?_⟩
    rw [abs_le]
    constructor <;> linarith

end
end Sude
