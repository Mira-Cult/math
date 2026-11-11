import Sude.PrefixPhysicalLineSum

/-! Recover physical distinctness from an injective installed pair supply. -/
namespace Sude
noncomputable section

/-- If each physical role was installed with an injective pair-slot value,
then two physical roles cannot occupy the same cell. -/
theorem prefixPhysicalCells_injective_of_placement {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (a : Cell n ≃ Fin (n * n))
    (values : ((Fin P × Fin Q) × Bool) → pool n) (hinj : Function.Injective values)
    (hplaced : ∀ x, entry a (prefixPhysicalCells hrect hs choice rows cols hrows hcols x) =
      (values (prefixPhysicalInput hfit hdiag x)).val) :
    Function.Injective (prefixPhysicalCells hrect hs choice rows cols hrows hcols) := by
  intro x y hxy
  apply prefixPhysicalInput_injective hfit hdiag
  apply hinj
  apply Subtype.ext
  rw [← hplaced x, ← hplaced y, hxy]

end
end Sude
