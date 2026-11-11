import Sude.CentralStockDepletion
namespace Sude
noncomputable section

/-- Sufficient old-reservation budget for DQ's widened interval. The cover,
outer-band membership, mean enclosure and separation are explicit inputs. -/
theorem old_reservation_widened_interval_from_bands {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (accounted shielded : Finset ℕ)
    (m σ ε w : ℝ) (Dold : ℕ) (hn : 0 < n) (hε : 0 ≤ ε)
    (hmean : |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - m| ≤ σ * poolMaximum n)
    (hgap : σ + ε + 3 / (4 * (n : ℝ)) + w < 1/4)
    (hleft : 1 ≤ m - (σ + ε + 3 / (4 * (n : ℝ))) * poolMaximum n)
    (hcover : reserved.image (entry a) ⊆ accounted ∪ shielded)
    (haccount : accounted.card ≤ Dold)
    (hband : ∀ p ∈ shielded, (p : ℝ) ≤ m - (poolMaximum n : ℝ)/4 + w * poolMaximum n ∨
      m + (poolMaximum n : ℝ)/4 - w * poolMaximum n ≤ p) :
    (apInterval
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n))
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n))
      2 1 ∩ reserved.image (entry a)).card ≤ Dold := by
  classical
  let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  let X : ℝ := poolMaximum n
  let e : ℝ := ε + 3 / (4 * (n : ℝ))
  let lo := μ - e*X
  let hi := μ + e*X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hrad : 0 ≤ e*X := mul_nonneg he hX.le
  have hm := abs_le.mp hmean
  have hlo : 1 ≤ lo := by dsimp [lo, e, μ, X] at *; nlinarith [hm.1]
  have hhi : 0 ≤ hi := by dsimp [hi, lo] at *; linarith
  have hprotect : ∀ p ∈ shielded, p ∉ apInterval lo hi 2 1 := by
    intro p hp hpi
    have hmem := (mem_apInterval_iff lo hi 2 1 (by linarith) hhi p).mp hpi
    have haway := central_window_avoids_outer_bands X m μ σ e w p hX hmean
      (by dsimp [e] at *; linarith) (hband p hp)
    exact haway ⟨hmem.2.1, hmem.2.2.1⟩
  have hdel := (interval_deletions_le_accounted lo hi (reserved.image (entry a)) accounted shielded
    hcover hprotect).trans haccount
  have hloeq : lo = μ - ε*X - 3*X/(4*(n : ℝ)) := by dsimp [lo,e]; ring
  have hhieq : hi = μ + ε*X + 3*X/(4*(n : ℝ)) := by dsimp [hi,e]; ring
  rw [hloeq, hhieq] at hdel
  exact hdel

/-- Translate source-mean margins to the endpoints of the exact old-mean
widened interval, keeping the enclosure as an explicit assumption. -/
theorem old_widened_endpoints_from_mean {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (m σ ε : ℝ)
    (hmean : |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - m| ≤ σ * poolMaximum n)
    (hleft : 1 ≤ m - (σ + ε + 3 / (4 * (n : ℝ))) * poolMaximum n)
    (hright : m + (σ + ε + 3 / (4 * (n : ℝ))) * poolMaximum n ≤ poolMaximum n) :
    1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n -
      3 * (poolMaximum n : ℝ) / (4*n) ∧
    centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n +
      3 * (poolMaximum n : ℝ) / (4*n) ≤ poolMaximum n := by
  have hm := abs_le.mp hmean
  have heq : (σ + ε + 3 / (4 * (n : ℝ))) * poolMaximum n =
      σ * poolMaximum n + ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4 * n) := by ring
  rw [heq] at hleft hright
  constructor <;> linarith [hm.1, hm.2, hleft, hright]

end
end Sude
