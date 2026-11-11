import Sude.ActualUnusedScreenedStock

/-! Exact transport of the actual unused pool across supplied squares with
the same role-value image. This does not identify a larger keepout set. -/
namespace Sude
noncomputable section

/-- Equal value images on the same physical role set leave the same actual
unused pool, even if the placements within the role set differ. -/
theorem actualUnusedPool_eq_of_role_value_image_eq {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (roles : Finset (Cell n))
    (hroles : roles.image (entry a) = roles.image (entry b)) :
    actualUnusedPool a roles = actualUnusedPool b roles := by
  apply (Finset.image_inj Subtype.val_injective).mp
  rw [actualUnusedPool_value_image_eq, actualUnusedPool_value_image_eq, hroles]

/-- The screened-stock decomposition transfers to another square when its
actual role-value image is equal to the first square's image. The low-value
correction remains explicit and need not be empty. -/
theorem actualUnusedPool_value_image_screened_stock_of_role_image_eq
    {n g Q P : ℕ} (a b : Cell n ≃ Fin (n * n)) (roles : Finset (Cell n))
    (early : Finset ℕ) {final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (hlen : stages.length = P)
    (trace : BTGrowingTrace g Q (((poolFinset n).filter (fun x => 43 < x)) \ early)
      radius final last stages)
    (hroles : roles.image (entry a) = early ∪ Finset.univ.biUnion
      (fun i : Fin P => (BTStageTrace.stageAt stages hlen i).footprint))
    (hequal : roles.image (entry a) = roles.image (entry b)) :
    (actualUnusedPool b roles).image Subtype.val =
      final ∪ (((poolFinset n).filter (fun x => x ≤ 43)) \ early) ∧
    Disjoint final (((poolFinset n).filter (fun x => x ≤ 43)) \ early) := by
  rw [← actualUnusedPool_eq_of_role_value_image_eq a b roles hequal]
  exact actualUnusedPool_value_image_eq_screened_stock_indexed a roles early hlen trace hroles

end
end Sude
