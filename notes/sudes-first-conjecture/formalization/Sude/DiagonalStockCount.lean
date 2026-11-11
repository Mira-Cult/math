import Sude.CentralPostInputs

/-! Bounded analytic supplies for the two diagonal selection windows. -/
namespace Sude
noncomputable section

/-- Genuine unused values in a half-open interval, measured in the actual
prescribed pool. -/
def unusedPoolWindow {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (lo hi : ℝ) : Finset (pool n) :=
  (actualUnusedPool a reserved).filter fun v => lo < centralPoolValue v ∧ centralPoolValue v ≤ hi

/-- Available prime values in a bounded q=2 interval inject into the actual
unused pool window. -/
theorem available_interval_le_unused_window {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (lo hi : ℝ)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hcap : hi ≤ poolMaximum n) :
    (availableInterval lo hi 2 1 (reserved.image (entry a))).card ≤
      (unusedPoolWindow a reserved lo hi).card := by
  classical
  let deleted := reserved.image (entry a)
  have hsub : availableInterval lo hi 2 1 deleted ⊆
      (unusedPoolWindow a reserved lo hi).image Subtype.val := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hpool := even_apInterval_subset_pool n lo hi 2 1 hlo hhi hcap (by decide) (by decide) p hp'.1
    let v : pool n := ⟨p, hpool⟩
    have hv : v ∈ actualUnusedPool a reserved := by
      apply (mem_actualUnusedPool a reserved v).2
      intro z hz heq
      exact hp'.2 (Finset.mem_image.mpr ⟨z, hz, heq.symm⟩)
    have hint := (mem_apInterval_iff lo hi 2 1 hlo hhi p).mp hp'.1
    refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hv, hint.2.1, hint.2.2.1⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  exact h

/-- BMOR's q=2 bound after charging only reserved values in the interval.
The deletion count is explicit and refers to the physical reservation. -/
theorem bmor_unused_window_count (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n : ℕ} (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (lo hi : ℝ) (D : ℕ) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hlo : 1 ≤ lo) (horder : lo ≤ hi) (hcap : hi ≤ poolMaximum n)
    (hdeleted : (apInterval lo hi 2 1 ∩ reserved.image (entry a)).card ≤ D) :
    ((hi - lo) - (518 / 125 : ℝ) * (Real.sqrt lo + Real.sqrt hi)) /
      Real.log (poolMaximum n) - D ≤ (unusedPoolWindow a reserved lo hi).card := by
  let deleted := reserved.image (entry a)
  have hs := bmor_two_pool_interval_supply bmor upper n lo hi hn hnmax hlo horder hcap
  have hsum := Finset.card_sdiff_add_card_inter (apInterval lo hi 2 1) deleted
  have hsum' : (availableInterval lo hi 2 1 deleted).card +
      (apInterval lo hi 2 1 ∩ deleted).card = (apInterval lo hi 2 1).card := hsum
  have hsumR : ((availableInterval lo hi 2 1 deleted).card : ℝ) +
      (apInterval lo hi 2 1 ∩ deleted).card = (apInterval lo hi 2 1).card := by exact_mod_cast hsum'
  have hdelR : ((apInterval lo hi 2 1 ∩ deleted).card : ℝ) ≤ D := by exact_mod_cast hdeleted
  have hstock := available_interval_le_unused_window a reserved lo hi (by linarith) (by linarith) hcap
  have hstockR : ((availableInterval lo hi 2 1 deleted).card : ℝ) ≤
      (unusedPoolWindow a reserved lo hi).card := by exact_mod_cast hstock
  linarith [hs.1]

/-- Two actual stock windows around `m`, each with its own explicit
reservation-deletion budget and numerical gate. -/
theorem bmor_two_diagonal_window_supplies (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n : ℕ} (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (m η : ℝ) (q Dlo Dhi : ℕ) (hη : 0 ≤ η) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hleft : 1 ≤ m - η) (hright : m + η ≤ poolMaximum n)
    (hdeletedLo : (apInterval (m - η) (m - η / 2) 2 1 ∩ reserved.image (entry a)).card ≤ Dlo)
    (hdeletedHi : (apInterval (m + η / 2) (m + η) 2 1 ∩ reserved.image (entry a)).card ≤ Dhi)
    (hgateLo : (q : ℝ) ≤ ((m - η / 2 - (m - η)) - (518 / 125 : ℝ) *
      (Real.sqrt (m - η) + Real.sqrt (m - η / 2))) / Real.log (poolMaximum n) - Dlo)
    (hgateHi : (q : ℝ) ≤ ((m + η - (m + η / 2)) - (518 / 125 : ℝ) *
      (Real.sqrt (m + η / 2) + Real.sqrt (m + η))) / Real.log (poolMaximum n) - Dhi) :
    q ≤ (unusedPoolWindow a reserved (m - η) (m - η / 2)).card ∧
      q ≤ (unusedPoolWindow a reserved (m + η / 2) (m + η)).card := by
  have hlo := bmor_unused_window_count bmor upper a reserved (m - η) (m - η / 2) Dlo hn hnmax
    hleft (by linarith) (by linarith) hdeletedLo
  have hhi := bmor_unused_window_count bmor upper a reserved (m + η / 2) (m + η) Dhi hn hnmax
    (by linarith) (by linarith) hright hdeletedHi
  constructor
  · have h : (q : ℝ) ≤ (unusedPoolWindow a reserved (m - η) (m - η / 2)).card := hgateLo.trans hlo
    exact_mod_cast h
  · have h : (q : ℝ) ≤ (unusedPoolWindow a reserved (m + η / 2) (m + η)).card := hgateHi.trans hhi
    exact_mod_cast h

/-- A single physical reservation is a sound deletion budget for every
window, without any disjointness or independence assumption. -/
theorem window_deletions_le_reserved_card {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (lo hi : ℝ) :
    (apInterval lo hi 2 1 ∩ reserved.image (entry a)).card ≤ reserved.card := by
  have h := Finset.card_le_card (Finset.inter_subset_right :
    apInterval lo hi 2 1 ∩ reserved.image (entry a) ⊆ reserved.image (entry a))
  rw [Finset.card_image_of_injective _ (entry_injective a)] at h
  exact h

end
end Sude
