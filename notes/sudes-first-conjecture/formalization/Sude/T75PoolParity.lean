import Sude.TargetRouting

/-! Exact parity and mean bookkeeping for the prescribed odd-prime pool.
These facts do not construct prime targets or estimate their discrepancies. -/
namespace Sude
noncomputable section

/-- At odd order, the prescribed pool has an odd number of odd entries, so
its exact total is odd. -/
theorem t75_pool_total_odd {n : ℕ} (hn : Odd n) : Odd (Lucas.poolTotal n) := by
  unfold Lucas.poolTotal
  exact odd_sum_of_odd_entries (hn.mul hn) (fun i : Fin (n * n) => oddPrime i.val)
    (fun i => oddPrime_odd i.val)

/-- The actual pool total has the same parity as the odd order. -/
theorem t75_pool_total_mod_two {n : ℕ} (hn : Odd n) :
    Lucas.poolTotal n % 2 = n % 2 := by
  have ht := Nat.odd_iff.mp (t75_pool_total_odd hn)
  have horder := Nat.odd_iff.mp hn
  omega

/-- The real mean line total multiplied by a positive order is exactly the
actual pool total; no rounding or approximation is involved. -/
theorem t75_pool_mean_line_total {n : ℕ} (hn : 0 < n) :
    ((Lucas.poolTotal n : ℝ) / (n : ℝ)) * (n : ℝ) = Lucas.poolTotal n := by
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  exact div_mul_cancel₀ _ h

/-- T75's mean line total is the order times the mean pool entry. -/
theorem t75_line_mean_eq_order_mul_pool_mean {n : ℕ} (hn : 0 < n) :
    (Lucas.poolTotal n : ℝ) / (n : ℝ) =
      (n : ℝ) * ((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) := by
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  push_cast
  field_simp

end
end Sude
