import Sude.EvenGrid

/-! Finite subset-sum grids with an arbitrary positive integer step. -/
namespace Sude
noncomputable section

/-- Every multiple of `step` through `R` is realized by distinct labels. -/
def CompleteStepGrid {α : Type*} (S : Finset α) (gap : α → ℕ) (step R : ℕ) : Prop :=
  ∀ t, t ≤ R → step ∣ t → ∃ T : Finset α, T ⊆ S ∧ (∑ i ∈ T, gap i) = t

/-- A multiple of the step larger than a step-multiple radius is at least
one whole step larger. -/
theorem step_multiple_next {step R t : ℕ} (_hs : 0 < step)
    (hR : step ∣ R) (ht : step ∣ t) (hlt : R < t) : R + step ≤ t := by
  obtain ⟨r, rfl⟩ := hR
  obtain ⟨z, rfl⟩ := ht
  have hrz : r < z := by
    by_contra hn
    have hzr : z ≤ r := by omega
    have hm := Nat.mul_le_mul_left step hzr
    omega
  have hm := Nat.mul_le_mul_left step (show r + 1 ≤ z by omega)
  simpa [Nat.mul_add] using hm

/-- A fresh step-multiple gap no larger than `R + step` extends the complete
physical subset-sum grid to `R + gap`. -/
theorem completeStepGrid_insert {α : Type*} [DecidableEq α]
    (S : Finset α) (gap : α → ℕ) (step R : ℕ) (k : α)
    (hs : 0 < step) (hk : k ∉ S) (hR : step ∣ R) (hgap : step ∣ gap k)
    (hjoin : gap k ≤ R + step) (hcomplete : CompleteStepGrid S gap step R) :
    CompleteStepGrid (insert k S) gap step (R + gap k) := by
  intro t ht hstep
  by_cases hsmall : t ≤ R
  · obtain ⟨T, hT, hsum⟩ := hcomplete t hsmall hstep
    exact ⟨T, hT.trans (Finset.subset_insert k S), hsum⟩
  · have hge : gap k ≤ t := le_trans hjoin (step_multiple_next hs hR hstep (by omega))
    have hrest : t - gap k ≤ R := by omega
    have hstepRest : step ∣ t - gap k := Nat.dvd_sub hstep hgap
    obtain ⟨T, hT, hsum⟩ := hcomplete (t - gap k) hrest hstepRest
    have hnot : k ∉ T := fun hmem => hk (hT hmem)
    refine ⟨insert k T, Finset.insert_subset_insert k hT, ?_⟩
    rw [Finset.sum_insert hnot, hsum]
    omega

/-- A chain records the actual accumulated radius after each added gap. -/
inductive StepGapChain {K : Type*} (gap : K → ℕ) (step : ℕ) : ℕ → List K → Prop
  | nil (R : ℕ) : StepGapChain gap step R []
  | cons (R : ℕ) (k : K) (ks : List K) :
      step ∣ gap k → gap k ≤ R + step → StepGapChain gap step (R + gap k) ks →
      StepGapChain gap step R (k :: ks)

/-- Extend a complete grid by a distinct chain of actual gap labels. -/
theorem extend_step_gap_chain {K : Type*} [DecidableEq K]
    (gap : K → ℕ) (step : ℕ) (base : Finset K) (R : ℕ) (ks : List K)
    (hs : 0 < step) (hbase : CompleteStepGrid base gap step R) (hR : step ∣ R)
    (hnodup : ks.Nodup) (hfresh : ∀ k ∈ ks, k ∉ base)
    (hchain : StepGapChain gap step R ks) :
    CompleteStepGrid (base ∪ ks.toFinset) gap step (R + (ks.map gap).sum) := by
  induction hchain generalizing base with
  | nil R => simpa using hbase
  | cons R k ks hkstep hjoin htail ih =>
    have hn : k ∉ ks := (List.nodup_cons.mp hnodup).1
    have hnd : ks.Nodup := (List.nodup_cons.mp hnodup).2
    have hk : k ∉ base := hfresh k (by simp)
    have hf : ∀ j ∈ ks, j ∉ insert k base := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, hfresh j (by simp [hj])⟩
      intro h
      subst j
      exact hn hj
    have hnew := completeStepGrid_insert base gap step R k hs hk hR hkstep hjoin hbase
    have hstepNew : step ∣ R + gap k := dvd_add hR hkstep
    have hresult := ih (insert k base) hnew hstepNew hnd hf
    simpa [List.toFinset_cons, Finset.union_insert, Finset.insert_union, add_assoc,
      add_comm, add_left_comm] using hresult

end
end Sude
