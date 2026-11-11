import Sude.CentralWindow

/-! Exact remaining-mean accounting for labelled finite stage selections.
No concentration or selection existence is asserted. -/
namespace Sude
noncomputable section

/-- Removing an exact number of labelled entries updates the remaining mean by
the selected sum's discrepancy. Distinct labels may carry equal values. -/
theorem prefix_remaining_mean_eq {α : Type*} [DecidableEq α]
    (A T : Finset α) (v : α → ℝ) (M r : ℕ)
    (hsub : T ⊆ A) (hM : A.card = M) (hr : T.card = r)
    (hpos : 0 < M - r) :
    (∑ x ∈ A \ T, v x) / ((M-r : ℕ) : ℝ) =
      (∑ x ∈ A, v x) / M -
        ((∑ x ∈ T, v x) - (r : ℝ) * ((∑ x ∈ A, v x) / M)) / ((M-r : ℕ) : ℝ) := by
  have hrM : r ≤ M := by rw [← hr, ← hM]; exact Finset.card_le_card hsub
  have hMpos : 0 < M := by omega
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hMpos)
  have hremR : ((M-r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hcast : ((M-r : ℕ) : ℝ) + r = M := by exact_mod_cast (show M-r+r=M by omega)
  have hsum := Finset.sum_sdiff (f := v) hsub
  field_simp
  rw [← hcast, ← hsum]
  ring

/-- Across equally sized stages, a second family's deviation from the
original means equals its deviation from the remaining means minus the
first family's aggregate discrepancy times `q/(M-r)`. -/
theorem prefix_second_selection_deviation {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (J : Finset ι) (A T U : ι → Finset α) (v : ι → α → ℝ)
    (M r q : ℕ)
    (hsub : ∀ j ∈ J, T j ⊆ A j)
    (hM : ∀ j ∈ J, (A j).card = M)
    (hr : ∀ j ∈ J, (T j).card = r)
    (_hU : ∀ j ∈ J, U j ⊆ A j \ T j)
    (_hq : ∀ j ∈ J, (U j).card = q)
    (hpos : 0 < M-r) :
    let μ := fun j => (∑ x ∈ A j, v j x) / M
    let μ' := fun j => (∑ x ∈ A j \ T j, v j x) / ((M-r : ℕ) : ℝ)
    let E := (∑ j ∈ J, ∑ x ∈ T j, v j x) - (r : ℝ) * (∑ j ∈ J, μ j)
    let ε := (∑ j ∈ J, ∑ x ∈ U j, v j x) - (q : ℝ) * (∑ j ∈ J, μ' j)
    (∑ j ∈ J, ∑ x ∈ U j, v j x) - (q : ℝ) * (∑ j ∈ J, μ j) =
      ε - ((q : ℝ) / ((M-r : ℕ) : ℝ)) * E := by
  dsimp only
  have hshift : ∑ j ∈ J, (∑ x ∈ A j \ T j, v j x) / ((M-r : ℕ) : ℝ) =
      (∑ j ∈ J, (∑ x ∈ A j, v j x) / M) -
        ((∑ j ∈ J, ∑ x ∈ T j, v j x) -
          (r : ℝ) * (∑ j ∈ J, (∑ x ∈ A j, v j x) / M)) / ((M-r : ℕ) : ℝ) := by
    calc
      _ = ∑ j ∈ J, ((∑ x ∈ A j, v j x) / M -
          ((∑ x ∈ T j, v j x) - (r : ℝ) * ((∑ x ∈ A j, v j x) / M)) / ((M-r : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact prefix_remaining_mean_eq (A j) (T j) (v j) M r (hsub j hj) (hM j hj) (hr j hj) hpos
      _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hshift]
  ring

/-- Successive labelled selections are disjoint and their cumulative
aggregate discrepancy obeys the exact remaining-mean recurrence. -/
theorem prefix_cumulative_selection_deviation {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (J : Finset ι) (A T U : ι → Finset α) (v : ι → α → ℝ)
    (M r q : ℕ)
    (hsub : ∀ j ∈ J, T j ⊆ A j)
    (hM : ∀ j ∈ J, (A j).card = M)
    (hr : ∀ j ∈ J, (T j).card = r)
    (hU : ∀ j ∈ J, U j ⊆ A j \ T j)
    (hq : ∀ j ∈ J, (U j).card = q)
    (hpos : 0 < M-r) :
    (∀ j ∈ J, Disjoint (T j) (U j) ∧ (T j ∪ U j).card = r+q) ∧
    let μ := fun j => (∑ x ∈ A j, v j x) / M
    let μ' := fun j => (∑ x ∈ A j \ T j, v j x) / ((M-r : ℕ) : ℝ)
    let E := (∑ j ∈ J, ∑ x ∈ T j, v j x) - (r : ℝ) * (∑ j ∈ J, μ j)
    let ε := (∑ j ∈ J, ∑ x ∈ U j, v j x) - (q : ℝ) * (∑ j ∈ J, μ' j)
    (∑ j ∈ J, ∑ x ∈ T j ∪ U j, v j x) - ((r+q : ℕ) : ℝ) * (∑ j ∈ J, μ j) =
      (1 - (q : ℝ) / ((M-r : ℕ) : ℝ)) * E + ε := by
  have hdis : ∀ j ∈ J, Disjoint (T j) (U j) := by
    intro j hj
    apply Finset.disjoint_left.mpr
    intro x hx hxu
    have h := hU j hj hxu
    exact (Finset.mem_sdiff.mp h).2 hx
  constructor
  · intro j hj
    exact ⟨hdis j hj, by rw [Finset.card_union_of_disjoint (hdis j hj), hr j hj, hq j hj]⟩
  · dsimp only
    have hsum : (∑ j ∈ J, ∑ x ∈ T j ∪ U j, v j x) =
        (∑ j ∈ J, ∑ x ∈ T j, v j x) + (∑ j ∈ J, ∑ x ∈ U j, v j x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_union (hdis j hj)
    rw [hsum]
    have h := prefix_second_selection_deviation J A T U v M r q hsub hM hr hU hq hpos
    dsimp only at h
    push_cast
    linarith

end
end Sude
