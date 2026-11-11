import Sude.NarrowSeedRetained

/-! Additional candidate pairs survive the retained seed reservation. -/
namespace Sude
noncomputable section

/-- A seed pair not used in the initial sorted candidate set shares no
endpoint with the retained reservation. The entire seed matching, not merely
the candidate subfamily, supplies the physical disjointness. -/
theorem unchosenSeedEndpoint_not_retained (seeds candidates : Finset ℕ)
    (r Q gap : ℕ) (hcard : candidates.card = r * Q)
    (hsub : candidates ⊆ seeds) (hmatch : PairwiseDisjointPairs seeds gap)
    (kept : Finset ℕ) (hkept : kept ⊆ Finset.range r)
    (p : ℕ) (hp : p ∈ seeds) (hnot : p ∉ candidates) (side : Bool) :
    pairEndpoint seeds gap (⟨p, hp⟩, side) ∉
      retainedSeedEndpoints candidates r Q gap hcard kept hkept := by
  intro hr
  obtain ⟨x, _, heq⟩ := Finset.mem_image.mp hr
  let q := sortedSeedLower candidates r Q hcard x.1
  have hq : q ∈ candidates := sortedSeedLower_mem candidates r Q hcard x.1
  have hpq : p ≠ q := by
    intro hpq
    exact hnot (hpq ▸ hq)
  have hdis := hmatch p hp q (hsub hq) hpq
  have hpentry := pairEndpoint_mem seeds gap (⟨p, hp⟩, side)
  have hqentry : sortedSeedEndpoint candidates r Q gap hcard x ∈ ({q, q + gap} : Finset ℕ) := by
    exact pairEndpoint_mem candidates gap (⟨q, hq⟩, x.2)
  rw [heq] at hqentry
  exact Finset.disjoint_left.mp hdis hpentry hqentry

end
end Sude
