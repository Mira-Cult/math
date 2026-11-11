import Sude.ActualUnusedScreenedStock

/-! Exact additional depletion when a physical reservation is enlarged from
the role cells to a supplied full keepout. No property of the values in the
additional cells is asserted. -/
namespace Sude
noncomputable section

/-- Enlarging the role reservation removes exactly the pool-subtype values
held by cells in the set difference `full \ roles`. -/
theorem actualUnusedPool_full_eq_roles_sdiff {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (roles full : Finset (Cell n))
    (hsub : roles ⊆ full) :
    actualUnusedPool a full = actualUnusedPool a roles \ (full \ roles).image (entryPool a) := by
  classical
  ext v
  rw [Finset.mem_sdiff, mem_actualUnusedPool, mem_actualUnusedPool]
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · intro z hz
      exact hv z (hsub hz)
    · intro hv'
      obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hv'
      have hvz : v.val = entry a z := by
        have he' := congrArg Subtype.val he
        simpa using he'.symm
      exact hv z (Finset.mem_sdiff.mp hz).1 hvz
  · rintro ⟨hrole, hnot⟩ z hz he
    by_cases hzr : z ∈ roles
    · exact hrole z hzr he
    · apply hnot
      refine Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, hzr⟩, ?_⟩
      exact Subtype.ext he.symm

/-- The same identity after forgetting pool subtypes; the removed values
are exactly the actual entries of the extra keepout cells. -/
theorem actualUnusedPool_full_value_image_eq_roles_sdiff {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (roles full : Finset (Cell n))
    (hsub : roles ⊆ full) :
    (actualUnusedPool a full).image Subtype.val =
      (actualUnusedPool a roles).image Subtype.val \ (full \ roles).image (entry a) := by
  rw [actualUnusedPool_full_eq_roles_sdiff a roles full hsub,
    Finset.image_sdiff _ _ Subtype.val_injective]
  congr 1
  simp only [Finset.image_image, Function.comp_def, entryPool_val]

/-- Under the supplied role-value and trace hypotheses, the full keepout
unused values are the screened decomposition with the extra keepout values
removed. No claim is made that those extra values are high or available. -/
theorem actualUnusedPool_full_value_image_eq_screened_sdiff
    {n g Q P : ℕ} (a : Cell n ≃ Fin (n * n)) (roles full : Finset (Cell n))
    (hsub : roles ⊆ full) (early : Finset ℕ) {final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage} (hlen : stages.length = P)
    (trace : BTGrowingTrace g Q (((poolFinset n).filter (fun x => 43 < x)) \ early)
      radius final last stages)
    (hroles : roles.image (entry a) = early ∪ Finset.univ.biUnion
      (fun i : Fin P => (BTStageTrace.stageAt stages hlen i).footprint)) :
    (actualUnusedPool a full).image Subtype.val =
      (final ∪ (((poolFinset n).filter (fun x => x ≤ 43)) \ early)) \
        (full \ roles).image (entry a) := by
  rw [actualUnusedPool_full_value_image_eq_roles_sdiff a roles full hsub]
  rw [(actualUnusedPool_value_image_eq_screened_stock_indexed a roles early hlen trace hroles).1]

end
end Sude
