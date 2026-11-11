import Sude.PhysicalPairLineSum
import Sude.PrefixAllocationCoverage

/-! Exact line sums for the actually installed prefix pair cells. -/
namespace Sude
noncomputable section

/-- Exact prefix capacity identifies each physical role with one pair slot
and endpoint orientation. -/
noncomputable def prefixPhysicalInputEquiv {P d layers n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q) :
    PrefixPhysicalInputs P d layers n ≃ (Fin P × Fin Q) × Bool :=
  Equiv.ofBijective (prefixPhysicalInput hfit hdiag) (prefixPhysicalInput_bijective hfit hdiag hexact)

/-- The actual physical cell occupied by a given prefix stage, pair slot,
and endpoint orientation. -/
noncomputable def prefixPairCells {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) : (Fin P × Fin Q) × Bool → Cell n :=
  fun x => prefixPhysicalCells hrect hs choice rows cols hrows hcols
    ((prefixPhysicalInputEquiv hfit hdiag hexact).symm x)

/-- No two stage/slot/endpoint labels denote the same physical cell. -/
theorem prefixPairCells_injective {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers)
    (hcells : Function.Injective (prefixPhysicalCells hrect hs choice rows cols hrows hcols)) :
    Function.Injective (prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols) :=
  hcells.comp (prefixPhysicalInputEquiv hfit hdiag hexact).symm.injective

/-- The value at each reindexed physical cell is the value of that same
original pair slot and endpoint. -/
theorem prefixPairCells_entry {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (a : Cell n ≃ Fin (n * n))
    (values : ((Fin P × Fin Q) × Bool) → pool n)
    (hplaced : ∀ x, entry a (prefixPhysicalCells hrect hs choice rows cols hrows hcols x) =
      (values (prefixPhysicalInput hfit hdiag x)).val) (x : (Fin P × Fin Q) × Bool) :
    entry a (prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols x) = (values x).val := by
  have h := hplaced ((prefixPhysicalInputEquiv hfit hdiag hexact).symm x)
  have he : prefixPhysicalInput hfit hdiag ((prefixPhysicalInputEquiv hfit hdiag hexact).symm x) = x :=
    (prefixPhysicalInputEquiv hfit hdiag hexact).apply_symm_apply x
  rw [he] at h
  exact h

/-- The sum on any labelled line over the actual selected prefix cells is
the sum of their actual midpoint weights and signed fixed half-gaps. Cells
outside the selected prefix family, including any center, are not omitted
from the final theorem: they remain a separate completion obligation. -/
theorem prefixPairCells_line_sum {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers)
    (hcells : Function.Injective (prefixPhysicalCells hrect hs choice rows cols hrows hcols))
    (a : Cell n ≃ Fin (n * n)) (values : ((Fin P × Fin Q) × Bool) → pool n) (gap : ℕ)
    (hgap : ∀ p, (values (p, true)).val = (values (p, false)).val + gap)
    (hplaced : ∀ x, entry a (prefixPhysicalCells hrect hs choice rows cols hrows hcols x) =
      (values (prefixPhysicalInput hfit hdiag x)).val)
    (line : Cell n → Prop) [DecidablePred line] :
    let cells := prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry a c : ℝ)) =
      ∑ p, (physicalPairLineWeight cells line p *
        (((values (p, false)).val + (values (p, true)).val : ℝ) / 2) +
      physicalPairLineOrientation cells line p * ((gap : ℝ) / 2)) := by
  classical
  dsimp only
  rw [physicalPair_line_sum_midpoint _ (prefixPairCells_injective hfit hdiag hexact hrect hs choice rows cols hrows hcols hcells) line a]
  apply Finset.sum_congr rfl
  intro p _
  rw [prefixPairCells_entry hfit hdiag hexact hrect hs choice rows cols hrows hcols a values hplaced,
    prefixPairCells_entry hfit hdiag hexact hrect hs choice rows cols hrows hcols a values hplaced]
  have hg : ((values (p, true)).val : ℝ) - (values (p, false)).val = gap := by
    have hh := hgap p
    have hh' : ((values (p, true)).val : ℝ) = (values (p, false)).val + gap := by exact_mod_cast hh
    linarith
  rw [hg]

end
end Sude
