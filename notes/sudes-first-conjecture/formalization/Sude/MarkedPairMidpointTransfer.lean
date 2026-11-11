import Sude.NetworkSwitches

/-! Pointwise and weighted midpoint transfer from explicit reserved or
same-pair endpoint-sum preservation. This is not a switch construction. -/
namespace Sude
noncomputable section

/-- A marked pair's natural-number endpoint sum is preserved if both its
cells are fixed in a reservation, or it coincides, possibly with the sides
reversed, with one of two pair families whose sums are known to be preserved. -/
theorem marked_pair_sum_preserved {n : ℕ} {I R C : Type*}
    (a b : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (marked : I × Bool → Cell n) (row : R × Bool → Cell n)
    (col : C × Bool → Cell n)
    (hfixed : ∀ c ∈ reserved, entry b c = entry a c)
    (hrow : ∀ r, entry b (row (r,false)) + entry b (row (r,true)) =
      entry a (row (r,false)) + entry a (row (r,true)))
    (hcol : ∀ c, entry b (col (c,false)) + entry b (col (c,true)) =
      entry a (col (c,false)) + entry a (col (c,true)))
    (hcover : ∀ i, (∀ side, marked (i,side) ∈ reserved) ∨
      (∃ (r : R) (rev : Bool), ∀ side, marked (i,side) = row (r, if rev then !side else side)) ∨
      (∃ (c : C) (rev : Bool), ∀ side, marked (i,side) = col (c, if rev then !side else side))) :
    ∀ i, entry b (marked (i,false)) + entry b (marked (i,true)) =
      entry a (marked (i,false)) + entry a (marked (i,true)) := by
  intro i
  rcases hcover i with hreserved | hrow' | hcol'
  · rw [hfixed _ (hreserved false), hfixed _ (hreserved true)]
  · obtain ⟨r, rev, heq⟩ := hrow'
    rw [heq false, heq true]
    cases rev <;> simpa [Nat.add_comm] using hrow r
  · obtain ⟨c, rev, heq⟩ := hcol'
    rw [heq false, heq true]
    cases rev <;> simpa [Nat.add_comm] using hcol c

/-- The same hypotheses preserve every marked real midpoint. -/
theorem marked_pair_midpoint_preserved {n : ℕ} {I R C : Type*}
    (a b : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (marked : I × Bool → Cell n) (row : R × Bool → Cell n)
    (col : C × Bool → Cell n)
    (hfixed : ∀ c ∈ reserved, entry b c = entry a c)
    (hrow : ∀ r, entry b (row (r,false)) + entry b (row (r,true)) =
      entry a (row (r,false)) + entry a (row (r,true)))
    (hcol : ∀ c, entry b (col (c,false)) + entry b (col (c,true)) =
      entry a (col (c,false)) + entry a (col (c,true)))
    (hcover : ∀ i, (∀ side, marked (i,side) ∈ reserved) ∨
      (∃ (r : R) (rev : Bool), ∀ side, marked (i,side) = row (r, if rev then !side else side)) ∨
      (∃ (c : C) (rev : Bool), ∀ side, marked (i,side) = col (c, if rev then !side else side))) :
    ∀ i, (((entry b (marked (i,false)) : ℝ) + entry b (marked (i,true))) / 2) =
      (((entry a (marked (i,false)) : ℝ) + entry a (marked (i,true))) / 2) := by
  intro i
  have h := marked_pair_sum_preserved a b reserved marked row col hfixed hrow hcol hcover i
  have h' : (entry b (marked (i,false)) : ℝ) + entry b (marked (i,true)) =
      (entry a (marked (i,false)) : ℝ) + entry a (marked (i,true)) := by exact_mod_cast h
  rw [h']

/-- Any finite weighted sum of the same marked midpoints is preserved, for
arbitrary fixed real weights. No sign or disjointness hypothesis is needed. -/
theorem marked_pair_weighted_midpoints_preserved {n : ℕ} {I : Type*}
    (a b : Cell n ≃ Fin (n*n)) (marked : I × Bool → Cell n)
    (T : Finset I) (w : I → ℝ)
    (hmid : ∀ i ∈ T, (((entry b (marked (i,false)) : ℝ) + entry b (marked (i,true))) / 2) =
      (((entry a (marked (i,false)) : ℝ) + entry a (marked (i,true))) / 2)) :
    (∑ i ∈ T, w i * (((entry b (marked (i,false)) : ℝ) + entry b (marked (i,true))) / 2)) =
      ∑ i ∈ T, w i * (((entry a (marked (i,false)) : ℝ) + entry a (marked (i,true))) / 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [hmid i hi]

end
end Sude
