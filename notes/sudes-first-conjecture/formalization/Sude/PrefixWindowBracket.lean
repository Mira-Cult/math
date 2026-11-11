import Sude.CentralWindow

/-! Endpoint mean brackets for sorted finite lists. Repeated values are allowed;
indices are labels. -/
namespace Sude
noncomputable section

/-- Compare the sums of two ordered labelled blocks by cross multiplication. -/
theorem ordered_label_block_sums (a b : ℕ → ℝ) (p q : ℕ)
    (h : ∀ i < p, ∀ j < q, a i ≤ b j) :
    (q : ℝ) * (∑ i ∈ Finset.range p, a i) ≤
      (p : ℝ) * (∑ j ∈ Finset.range q, b j) := by
  have H : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, a i) ≤
      ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, b j := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact h i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  simpa [Finset.mul_sum, Finset.sum_mul, mul_comm] using H

/-- A sorted labelled population's first and last `k` windows bracket `k`
times its arithmetic mean. Ties are allowed; `k = 0` and `k = N` are included. -/
theorem prefix_window_brackets_mean (v : ℕ → ℝ) (N k : ℕ)
    (hN : 0 < N) (hk : k ≤ N)
    (hsorted : ∀ i j, i ≤ j → j < N → v i ≤ v j) :
    centralWindow v k 0 ≤ (k : ℝ) * ((∑ i ∈ Finset.range N, v i) / N) ∧
      (k : ℝ) * ((∑ i ∈ Finset.range N, v i) / N) ≤ centralWindow v k (N-k) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdecomp : (∑ i ∈ Finset.range N, v i) =
      (∑ i ∈ Finset.range k, v i) + (∑ i ∈ Finset.range (N-k), v (k+i)) := by
    have heq : k + (N-k) = N := by omega
    simpa only [heq] using (Finset.sum_range_add v k (N-k))
  have hlo := ordered_label_block_sums v (fun i => v (k+i)) k (N-k) (by
    intro i hi j hj
    apply hsorted i (k+j) (by omega) (by omega))
  have hdecomp' : (∑ i ∈ Finset.range N, v i) =
      (∑ i ∈ Finset.range (N-k), v i) + (∑ i ∈ Finset.range k, v (N-k+i)) := by
    have heq : (N-k) + k = N := by omega
    simpa only [heq] using (Finset.sum_range_add v (N-k) k)
  have hhi := ordered_label_block_sums v (fun i => v (N-k+i)) (N-k) k (by
    intro i hi j hj
    apply hsorted i (N-k+j) (by omega) (by omega))
  have hd : ((N-k : ℕ) : ℝ) + k = N := by exact_mod_cast (show N-k+k=N by omega)
  have hfirst : centralWindow v k 0 = ∑ i ∈ Finset.range k, v i := by
    simp [centralWindow]
  have hlast : centralWindow v k (N-k) = ∑ i ∈ Finset.range k, v (N-k+i) := by
    unfold centralWindow
    simpa using (Finset.sum_Ico_eq_sum_range v (N-k) (N-k+k))
  rw [hfirst, hlast, ← mul_div_assoc]
  constructor
  · apply (le_div_iff₀ hNR).2
    rw [hdecomp, ← hd]
    nlinarith
  · apply (div_le_iff₀ hNR).2
    rw [hdecomp', ← hd]
    nlinarith

end
end Sude
