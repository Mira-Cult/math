import Sude.PrefixGlobalCrossing
import Sude.PrefixWindowBracket

/-! Simultaneous fixed-cardinality selection from stage windows. Numerical
values may coincide; selections consist of labels (indices). -/
namespace Sude
noncomputable section

/-- From bracketed first/last windows, choose exactly `k` labels in each
stage with a single `C/2` aggregate error, not one error per stage. -/
theorem prefix_global_window_select {J : Type*} [Fintype J] [DecidableEq J]
    (M : J → ℕ) (k : ℕ) (v : J → ℕ → ℝ) (ν : J → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hk : ∀ j, k ≤ M j)
    (hwidth : ∀ j i l, i < M j → l < M j → v j l - v j i ≤ C)
    (hleft : ∀ j, centralWindow (v j) k 0 ≤ (k : ℝ) * ν j)
    (hright : ∀ j, (k : ℝ) * ν j ≤ centralWindow (v j) k (M j - k)) :
    ∃ T : J → Finset ℕ,
      (∀ j, T j ⊆ Finset.range (M j) ∧ (T j).card = k) ∧
      |(∑ j, ∑ i ∈ T j, v j i) - (k : ℝ) * (∑ j, ν j)| ≤ C / 2 := by
  classical
  let m : J → ℕ := fun j => M j - k
  let w : ∀ j, Fin (m j + 1) → ℝ := fun j i => centralWindow (v j) k i.val
  have hl : (∑ j, w j ⟨0, by omega⟩) ≤ (k : ℝ) * (∑ j, ν j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hleft j)
  have hr : (k : ℝ) * (∑ j, ν j) ≤ ∑ j, w j ⟨m j, by omega⟩ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hright j)
  have hjump : ∀ j (i : Fin (m j + 1)) (hi : i.val < m j),
      w j ⟨i.val + 1, by omega⟩ - w j i ≤ C := by
    intro j i hi
    change centralWindow (v j) k (i.val + 1) - centralWindow (v j) k i.val ≤ C
    rw [centralWindow_step]
    apply hwidth j
    · dsimp [m] at hi; omega
    · dsimp [m] at hi; have := hk j; omega
  obtain ⟨p, hp⟩ := prefix_global_path_near m w ((k : ℝ) * ∑ j, ν j) C hC hl hr hjump
  let T : J → Finset ℕ := fun j => Finset.Ico (p j).val ((p j).val + k)
  refine ⟨T, ?_, ?_⟩
  · intro j
    constructor
    · intro i hi
      have hi' := Finset.mem_Ico.mp hi
      apply Finset.mem_range.mpr
      have hj := (p j).isLt
      dsimp [m] at hj
      have := hk j
      omega
    · simp [T]
  · simpa [T, w, centralWindow] using hp

/-- PD2 for sorted indexed stage populations, retaining labels even when
values tie. The mean is taken over the whole original stage; no positive-size
assumption is needed when `k = 0`; in the empty case Lean totalizes
division by zero and the mean term is multiplied by zero. -/
theorem prefix_global_fixed_cardinality_select {J : Type*} [Fintype J] [DecidableEq J]
    (M : J → ℕ) (k : ℕ) (v : J → ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hk : ∀ j, k ≤ M j)
    (hsorted : ∀ j i l, i ≤ l → l < M j → v j i ≤ v j l)
    (hwidth : ∀ j i l, i < M j → l < M j → v j l - v j i ≤ C) :
    ∃ T : J → Finset ℕ,
      (∀ j, T j ⊆ Finset.range (M j) ∧ (T j).card = k) ∧
      |(∑ j, ∑ i ∈ T j, v j i) -
        (k : ℝ) * ∑ j, ((∑ i ∈ Finset.range (M j), v j i) / M j)| ≤ C / 2 := by
  classical
  by_cases hk0 : k = 0
  · subst k
    refine ⟨fun _ => ∅, ?_, ?_⟩
    · simp
    · simpa using div_nonneg hC (by norm_num : (0 : ℝ) ≤ 2)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let ν : J → ℝ := fun j => (∑ i ∈ Finset.range (M j), v j i) / M j
    have hbracket : ∀ j, centralWindow (v j) k 0 ≤ (k : ℝ) * ν j ∧
        (k : ℝ) * ν j ≤ centralWindow (v j) k (M j - k) := by
      intro j
      exact prefix_window_brackets_mean (v j) (M j) k (by have := hk j; omega)
        (hk j) (hsorted j)
    exact prefix_global_window_select M k v ν C hC hk hwidth
      (fun j => (hbracket j).1) (fun j => (hbracket j).2)

end
end Sude
