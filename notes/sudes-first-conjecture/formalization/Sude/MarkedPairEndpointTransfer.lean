import Sude.NetworkSwitches

/-! Lifting exact identity-or-reversal endpoint relations from the two network
families to marked pairs. No reference or later switch is constructed here. -/
namespace Sude
noncomputable section

/-- The two marked cells retain their original endpoint values, either in the
same order or reversed. This is stronger than pair-sum preservation. -/
def pairEndpointSameOrSwapped {n : ℕ} (a b : Cell n ≃ Fin (n*n))
    (x y : Cell n) : Prop :=
  (entry b x = entry a x ∧ entry b y = entry a y) ∨
  (entry b x = entry a y ∧ entry b y = entry a x)

/-- Fixed reserved cells or exact side-preserving coverage by a network pair
lift the network's identity-or-reversal relation to every marked pair. The
network and marked hypotheses refer to the same two supplied squares. -/
theorem marked_pair_endpoints_preserved {n : ℕ} {I R C : Type*}
    (a b : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (marked : I × Bool → Cell n) (row : R × Bool → Cell n)
    (col : C × Bool → Cell n)
    (hfixed : ∀ c ∈ reserved, entry b c = entry a c)
    (hrow : ∀ r, pairEndpointSameOrSwapped a b (row (r,false)) (row (r,true)))
    (hcol : ∀ c, pairEndpointSameOrSwapped a b (col (c,false)) (col (c,true)))
    (hcover : ∀ i, (∀ side, marked (i,side) ∈ reserved) ∨
      (∃ r, ∀ side, marked (i,side) = row (r,side)) ∨
      (∃ c, ∀ side, marked (i,side) = col (c,side))) :
    ∀ i, pairEndpointSameOrSwapped a b (marked (i,false)) (marked (i,true)) := by
  intro i
  rcases hcover i with hreserve | hrow' | hcol'
  · exact Or.inl ⟨hfixed _ (hreserve false), hfixed _ (hreserve true)⟩
  · obtain ⟨r,hr⟩ := hrow'
    rw [hr false, hr true]
    exact hrow r
  · obtain ⟨c,hc⟩ := hcol'
    rw [hc false, hc true]
    exact hcol c

/-- Under identity or reversal, the absolute signed integer endpoint gap is
unchanged. Its sign may reverse. -/
theorem pair_endpoint_gap_magnitude_preserved {n : ℕ}
    (a b : Cell n ≃ Fin (n*n)) (x y : Cell n)
    (h : pairEndpointSameOrSwapped a b x y) :
    |(entry b y : ℤ) - entry b x| = |(entry a y : ℤ) - entry a x| := by
  rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rw [hx,hy]
  · rw [hx,hy, abs_sub_comm]

end
end Sude
