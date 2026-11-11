import Sude.APStage

/-! Narrow a physical candidate batch without deleting unused candidates. -/
namespace Sude
noncomputable section

/-- If `z * Q` distinct lower endpoints lie in an interval of length
`z * width`, some real-width bin contains `Q` of them. The retained batch
has pairwise midpoint spread below `width` for any common gap, and every
unretained candidate remains available. -/
theorem narrow_candidate_batch (candidates : Finset ℕ) (lo width : ℝ) (z Q : ℕ)
    (hz : 0 < z) (hwidth : 0 < width)
    (hspan : ∀ p ∈ candidates, lo ≤ p ∧ (p : ℝ) < lo + z * width)
    (hcount : z * Q ≤ candidates.card) :
    ∃ chosen : Finset ℕ, chosen ⊆ candidates ∧ chosen.card = Q ∧
      ∀ p ∈ chosen, ∀ q ∈ chosen, |(p : ℝ) - q| < width := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    exact ⟨∅, by simp, by simp, by simp⟩
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ
  let key : ℕ → ℕ := fun p => ⌊((p : ℝ) - lo) / width⌋₊
  let fiber : ℕ → Finset ℕ := fun b => candidates.filter fun p => key p = b
  have hkey : ∀ p ∈ candidates, key p ∈ Finset.range z := by
    intro p hp
    apply Finset.mem_range.mpr
    have h := hspan p hp
    have hnonneg : 0 ≤ ((p : ℝ) - lo) / width := div_nonneg (by linarith) hwidth.le
    apply (Nat.floor_lt hnonneg).2
    apply (div_lt_iff₀ hwidth).2
    linarith
  have hsum : candidates.card = ∑ b ∈ Finset.range z, (fiber b).card :=
    Finset.card_eq_sum_card_fiberwise (s := candidates) (t := Finset.range z) (f := key) hkey
  have hsome : ∃ b ∈ Finset.range z, Q ≤ (fiber b).card := by
    by_contra hn
    have hsmall : ∀ b ∈ Finset.range z, (fiber b).card ≤ Q - 1 := by
      intro b hb
      have hb' : ¬ Q ≤ (fiber b).card := by
        intro h
        exact hn ⟨b, hb, h⟩
      omega
    have hsumle := Finset.sum_le_sum hsmall
    have hsumle' : candidates.card ≤ z * (Q - 1) := by
      rw [hsum]
      simpa using hsumle
    have hlt : z * (Q - 1) < z * Q := Nat.mul_lt_mul_of_pos_left (by omega) hz
    omega
  obtain ⟨b, hb, hlarge⟩ := hsome
  obtain ⟨chosen, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hsub' : chosen ⊆ candidates := hsub.trans (Finset.filter_subset _ _)
  refine ⟨chosen, hsub', hcard, ?_⟩
  intro p hp q hq
  have hpkey := (Finset.mem_filter.mp (hsub hp)).2
  have hqkey := (Finset.mem_filter.mp (hsub hq)).2
  have hbin : key p = key q := hpkey.trans hqkey.symm
  have hq_p := same_spatial_bin_gap hwidth (hspan p (hsub' hp)).1 hbin
  have hp_q := same_spatial_bin_gap hwidth (hspan q (hsub' hq)).1 hbin.symm
  apply abs_lt.mpr
  constructor <;> linarith

/-- For a common gap, the midpoint difference is exactly the lower-endpoint
 difference; narrowing therefore controls actual pair midpoints. -/
theorem narrow_common_gap_midpoints (p q h : ℕ) :
    (((p : ℝ) + (p + h : ℕ)) / 2) - (((q : ℝ) + (q + h : ℕ)) / 2) = (p : ℝ) - q := by
  push_cast
  ring

/-- Retain a narrow `Q`-batch from `zQ` actual disjoint pairs and charge
only the `2Q` endpoints that are really kept. -/
theorem narrow_matching_and_deplete (unused candidates : Finset ℕ)
    (lo width : ℝ) (z Q h : ℕ) (hz : 0 < z) (hwidth : 0 < width) (hh : 0 < h)
    (hspan : ∀ p ∈ candidates, lo ≤ p ∧ (p : ℝ) < lo + z * width)
    (hcount : z * Q ≤ candidates.card)
    (havailable : ∀ p ∈ candidates, p ∈ unused ∧ p + h ∈ unused)
    (hmatch : PairwiseDisjointPairs candidates h) :
    ∃ chosen : Finset ℕ, chosen ⊆ candidates ∧ chosen.card = Q ∧
      PairwiseDisjointPairs chosen h ∧ pairFootprint chosen h ⊆ unused ∧
      (pairFootprint chosen h).card = 2 * Q ∧
      (unused \ pairFootprint chosen h).card + 2 * Q = unused.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + h : ℕ)) / 2) - (((q : ℝ) + (q + h : ℕ)) / 2)| < width) := by
  obtain ⟨chosen, hsub, hcard, hnarrow⟩ :=
    narrow_candidate_batch candidates lo width z Q hz hwidth hspan hcount
  have hm : PairwiseDisjointPairs chosen h := by
    intro p hp q hq hpq
    exact hmatch p (hsub hp) q (hsub hq) hpq
  have hs : pairFootprint chosen h ⊆ unused := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (havailable v (hsub hv)).1
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      exact (havailable p (hsub hp)).2
  have hf : (pairFootprint chosen h).card = 2 * Q := by
    rw [pairFootprint_card chosen h hh hm, hcard]
  have hremaining := Finset.card_sdiff_add_card_eq_card hs
  rw [hf] at hremaining
  refine ⟨chosen, hsub, hcard, hm, hs, hf, hremaining, ?_⟩
  intro p hp q hq
  rw [narrow_common_gap_midpoints]
  exact hnarrow p hp q hq

end
end Sude
