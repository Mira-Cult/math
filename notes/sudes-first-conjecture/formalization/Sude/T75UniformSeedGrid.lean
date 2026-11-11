import Sude.StepGrid

/-! T75's uniform seed copies and a supplied fresh chain of coordinate
labels. Distinct labels may carry repeated endpoint values; no prime supply or
chain existence is asserted. -/
namespace Sude
noncomputable section

theorem t75_uniform_seed_grid {K : Type*} [DecidableEq K]
    (gap : K → ℕ) (h : ℕ) (seed : Finset K) (hh : 0 < h)
    (hseed : ∀ i ∈ seed, gap i = h) :
    CompleteStepGrid seed gap h (∑ i ∈ seed, gap i) := by
  induction seed using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro t ht _
    have : t = 0 := by omega
    subst t
    exact ⟨∅, by simp, by simp⟩
  | @insert a s ha ih =>
    have has : gap a = h := hseed a (by simp)
    have hss : ∀ i ∈ s, gap i = h := by
      intro i hi
      exact hseed i (by simp [hi])
    have hd : h ∣ ∑ i ∈ s, gap i := by
      apply Finset.dvd_sum
      intro i hi
      rw [hss i hi]
    have hc := completeStepGrid_insert s gap h (∑ i ∈ s, gap i) a hh ha hd
      (by rw [has]) (by rw [has]; omega) (ih hss)
    simpa [Finset.sum_insert ha, Nat.add_comm] using hc

theorem t75_uniform_seed_sum {K : Type*} [DecidableEq K]
    (gap : K → ℕ) (h : ℕ) (seed : Finset K)
    (hseed : ∀ i ∈ seed, gap i = h) :
    (∑ i ∈ seed, gap i) = seed.card * h := by
  calc
    (∑ i ∈ seed, gap i) = ∑ _i ∈ seed, h := Finset.sum_congr rfl hseed
    _ = seed.card * h := by simp

theorem t75_uniform_seed_extend {K : Type*} [DecidableEq K]
    (gap : K → ℕ) (h : ℕ) (seed : Finset K) (labels : List K)
    (hh : 0 < h) (hseed : ∀ i ∈ seed, gap i = h)
    (hnodup : labels.Nodup) (hfresh : ∀ i ∈ labels, i ∉ seed)
    (hchain : StepGapChain gap h (∑ i ∈ seed, gap i) labels) :
    CompleteStepGrid (seed ∪ labels.toFinset) gap h
      (∑ i ∈ seed ∪ labels.toFinset, gap i) := by
  have hd : h ∣ ∑ i ∈ seed, gap i := by
    apply Finset.dvd_sum
    intro i hi
    rw [hseed i hi]
  have hc := extend_step_gap_chain gap h seed (∑ i ∈ seed, gap i) labels hh
    (t75_uniform_seed_grid gap h seed hh hseed) hd hnodup hfresh hchain
  have hdis : Disjoint seed labels.toFinset := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact hfresh i (by simpa using hj) hi
  rw [Finset.sum_union hdis]
  simpa [List.sum_toFinset _ hnodup] using hc

end
end Sude
