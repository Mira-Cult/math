import Sude.FTTBounds
import Sude.Statement
import Sude.PrimeIndex

/-! The FTT row determines an actual list of labelled line targets. Pool
identity remains an explicit hypothesis until the prefix sieve is verified. -/
namespace Sude.Lucas
noncomputable section

def targetList (r : TargetRow) : List ℕ :=
  List.replicate (r.order - 2) r.common ++ [r.penultimate, r.last]

theorem targetList_length (r : TargetRow) (h : TargetRowValid r) :
    (targetList r).length = r.order := by
  have hn : 3 ≤ r.order := h.2.2.2.1
  simp [targetList]
  omega

theorem targetList_sum (r : TargetRow) (h : TargetRowValid r) :
    (targetList r).sum = r.total := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsum, _, _, _, _, _⟩
  simpa [targetList, nsmul_eq_mul, add_assoc] using hsum

theorem targetList_prime (r : TargetRow) (h : TargetRowValid r) :
    ∀ p ∈ targetList r, Nat.Prime p := by
  intro p hp
  simp only [targetList, List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with ⟨_, rfl⟩ | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

/-- The exact sum of the prescribed entries, independent of a placement. -/
def poolTotal (n : ℕ) : ℕ := ∑ i : Fin (n * n), oddPrime i.val

theorem placement_total (n : ℕ) (a : Cell n ≃ Fin (n * n)) :
    (∑ c : Cell n, entry a c) = poolTotal n := by
  unfold entry poolTotal
  exact Equiv.sum_comp a (fun i : Fin (n * n) => oddPrime i.val)

/-- If an FTT row's literal total has been identified with the prescribed
pool total, its target list has exactly the required global sum. -/
theorem targetList_matches_pool (r : TargetRow) (h : TargetRowValid r)
    (hpool : r.total = poolTotal r.order) :
    (targetList r).length = r.order ∧
    (∀ p ∈ targetList r, Nat.Prime p) ∧
    (targetList r).sum = poolTotal r.order := by
  exact ⟨targetList_length r h, targetList_prime r h,
    (targetList_sum r h).trans hpool⟩

/-- The target list, indexed by all labelled rows or columns. -/
def targetAt (r : TargetRow) (h : TargetRowValid r) (i : Fin r.order) : ℕ :=
  (targetList r).get ((finCongr (targetList_length r h).symm) i)

theorem targetAt_prime (r : TargetRow) (h : TargetRowValid r) (i : Fin r.order) :
    Nat.Prime (targetAt r h i) := by
  apply targetList_prime r h
  exact List.get_mem _ _

theorem targetAt_odd (r : TargetRow) (h : TargetRowValid r) (i : Fin r.order) :
    targetAt r h i % 2 = 1 := by
  have hmem : targetAt r h i ∈ targetList r := List.get_mem _ _
  simp only [targetList, List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hq, hp, hr, _, _, _, _, _, _⟩
  rcases hmem with ⟨_, heq⟩ | heq | heq
  · simpa [heq] using hq
  · simpa [heq] using hp
  · simpa [heq] using hr

theorem targetAt_radius (r : TargetRow) (h : TargetRowValid r) (i : Fin r.order) :
    |(targetAt r h i : ℝ) - (r.total : ℝ) / r.order| ≤ (r.maxEntry : ℝ) / 1000 := by
  have hmem : targetAt r h i ∈ targetList r := List.get_mem _ _
  simp only [targetList, List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  obtain ⟨hq, hp, hr⟩ := targetRowValid_real_radius h
  rcases hmem with ⟨_, heq⟩ | heq | heq
  · simpa [heq] using hq
  · simpa [heq] using hp
  · simpa [heq] using hr

theorem targetAt_sum (r : TargetRow) (h : TargetRowValid r) :
    (∑ i : Fin r.order, targetAt r h i) = r.total := by
  let e : Fin r.order ≃ Fin (targetList r).length :=
    finCongr (targetList_length r h).symm
  have hget : (∑ i : Fin (targetList r).length, (targetList r).get i) =
      (targetList r).sum := by
    rw [← List.sum_ofFn, List.ofFn_get]
  calc
    (∑ i : Fin r.order, targetAt r h i) =
        ∑ i : Fin (targetList r).length, (targetList r).get i := by
      exact Equiv.sum_comp e (targetList r).get
    _ = (targetList r).sum := hget
    _ = r.total := targetList_sum r h

theorem sum_rowSums (n : ℕ) (a : Cell n ≃ Fin (n * n)) :
    (∑ i : Fin n, rowSum a i) = poolTotal n := by
  rw [← placement_total n a]
  exact (Fintype.sum_prod_type (entry a)).symm

theorem sum_columnSums (n : ℕ) (a : Cell n ≃ Fin (n * n)) :
    (∑ i : Fin n, columnSum a i) = poolTotal n := by
  rw [← sum_rowSums n a]
  simp only [rowSum, columnSum]
  exact Finset.sum_comm

/-- A single source target list is compatible with both the row and column
axis totals, once the recorded total is proved to be the actual pool total.
This does not establish any per-line correction or diagonal compatibility. -/
theorem targetAt_axis_compatibility (r : TargetRow) (h : TargetRowValid r)
    (a : Cell r.order ≃ Fin (r.order * r.order))
    (hpool : r.total = poolTotal r.order) :
    (∑ i : Fin r.order, targetAt r h i) = ∑ i, rowSum a i ∧
    (∑ i : Fin r.order, targetAt r h i) = ∑ i, columnSum a i := by
  rw [targetAt_sum r h, sum_rowSums, sum_columnSums]
  exact ⟨hpool, hpool⟩

/-- The FTT primes, actual real-radius bounds, both axis totals and the
prime diagonal target, all under the two exact pool-identification premises.
The theorem does not assume or prove per-line diagonal compatibility. -/
theorem pool_target_system (r : TargetRow) (h : TargetRowValid r)
    (a : Cell r.order ≃ Fin (r.order * r.order))
    (hT : r.total = poolTotal r.order) (hX : r.maxEntry = poolMaximum r.order) :
    (∀ i : Fin r.order, Nat.Prime (targetAt r h i) ∧ targetAt r h i % 2 = 1 ∧
      |(targetAt r h i : ℝ) - (poolTotal r.order : ℝ) / r.order| ≤
        (poolMaximum r.order : ℝ) / 1000) ∧
    (∑ i : Fin r.order, targetAt r h i) = ∑ i, rowSum a i ∧
    (∑ i : Fin r.order, targetAt r h i) = ∑ i, columnSum a i ∧
    Nat.Prime r.common ∧ r.common % 2 = 1 ∧
      |(r.common : ℝ) - (poolTotal r.order : ℝ) / r.order| ≤
        (poolMaximum r.order : ℝ) / 1000 := by
  have hc : Nat.Prime r.common := h.1
  have hcodd : r.common % 2 = 1 := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hc_radius := (targetRowValid_real_radius h).1
  have haxis := targetAt_axis_compatibility r h a hT
  refine ⟨?_, haxis.1, haxis.2, hc, hcodd, ?_⟩
  · intro i
    refine ⟨targetAt_prime r h i, targetAt_odd r h i, ?_⟩
    simpa only [hT, hX] using targetAt_radius r h i
  · simpa only [hT, hX] using hc_radius

end
end Sude.Lucas
