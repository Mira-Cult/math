import Sude.NarrowSeedPhysical

/-! Exact physical reservation for retained sorted seed groups. -/
namespace Sude
noncomputable section

/-- The selected natural group labels, retyped as bounded group indices. -/
def retainedSeedGroups (r : ℕ) (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) : Finset (Fin r) :=
  kept.attach.image (fun j => ⟨j.val, Finset.mem_range.mp (hsub j.property)⟩)

theorem retainedSeedGroups_card (r : ℕ) (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) :
    (retainedSeedGroups r kept hsub).card = kept.card := by
  unfold retainedSeedGroups
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Subtype.ext
    exact congrArg Fin.val hab

/-- The source retains both endpoints of each slot in each selected group. -/
def retainedSeedLabels (r Q : ℕ) (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) :
    Finset ((Fin r × Fin Q) × Bool) :=
  (retainedSeedGroups r kept hsub ×ˢ Finset.univ) ×ˢ Finset.univ

theorem retainedSeedLabels_card (r Q : ℕ) (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) :
    (retainedSeedLabels r Q kept hsub).card = 2 * Q * kept.card := by
  simp [retainedSeedLabels, retainedSeedGroups_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Exact reservation set of retained endpoints, with no duplicate entry. -/
def retainedSeedEndpoints (candidates : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) : Finset ℕ :=
  (retainedSeedLabels r Q kept hsub).image (sortedSeedEndpoint candidates r Q gap hcard)

theorem retainedSeedEndpoints_card (candidates : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q) (hgap : 0 < gap)
    (hmatch : PairwiseDisjointPairs candidates gap)
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) :
    (retainedSeedEndpoints candidates r Q gap hcard kept hsub).card = 2 * Q * kept.card := by
  rw [retainedSeedEndpoints, Finset.card_image_of_injective _
    (sortedSeedEndpoint_injective candidates r Q gap hcard hgap hmatch)]
  exact retainedSeedLabels_card r Q kept hsub

theorem retainedSeedEndpoints_available (candidates pool reserved : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q)
    (havailable : pairFootprint candidates gap ⊆ pool \ reserved)
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) :
    retainedSeedEndpoints candidates r Q gap hcard kept hsub ⊆ pool \ reserved := by
  intro p hp
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
  exact sortedSeedEndpoint_available candidates pool reserved r Q gap hcard havailable x

/-- Membership in the bounded group set is exactly membership in the
original set of natural group labels. -/
theorem mem_retainedSeedGroups (r : ℕ) (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r)
    (j : Fin r) : j ∈ retainedSeedGroups r kept hsub ↔ j.val ∈ kept := by
  constructor
  · intro hj
    obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hj
    have heq : i.val = j.val := congrArg Fin.val hEq
    exact heq ▸ i.property
  · intro hj
    apply Finset.mem_image.mpr
    refine ⟨⟨j.val, hj⟩, Finset.mem_attach _ _, ?_⟩
    exact Fin.ext rfl

/-- Every endpoint from a discarded group remains outside the retained
reservation. This uses global injectivity, including across group boundaries. -/
theorem discardedSeedEndpoint_not_retained (candidates : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r)
    (x : (Fin r × Fin Q) × Bool) (hdiscard : x.1.1.val ∉ kept) :
    sortedSeedEndpoint candidates r Q gap hcard x ∉
      retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  intro hx
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
  have hyx : y = x := hinj heq
  subst y
  have hgroup : x.1.1 ∈ retainedSeedGroups r kept hsub := by
    have h1 := (Finset.mem_product.mp hy).1
    exact (Finset.mem_product.mp h1).1
  exact hdiscard ((mem_retainedSeedGroups r kept hsub x.1.1).mp hgroup)

end
end Sude
