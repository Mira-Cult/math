import Sude.ReferenceCompletionInvoiceTransport
import Sude.LayerTranspose

/-! Rebase a physical row network on a completion which fixes all its pair
endpoints. No assertion about the existence of a later flow is made. -/
namespace Sude
noncomputable section

/-- The same physical network pairs on a square with unchanged endpoints. -/
def rowNetworkPairsRebase {n : ℕ} {K : Type*} {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs K a) (c : Cell n ≃ Fin (n*n))
    (hfix : ∀ k side, entry c (rowNetworkSlot v (k,side)) = entry a (rowNetworkSlot v (k,side))) :
    RowNetworkPairs K c where
  low := v.low
  high := v.high
  column := v.column
  rows_ne := v.rows_ne
  gap := v.gap
  gap_at := by
    intro k
    have h₀ := hfix k false
    have h₁ := hfix k true
    simp only [rowNetworkSlot, Bool.false_eq_true, ↓reduceIte] at h₀ h₁
    rw [h₀, h₁]
    exact v.gap_at k
  slots_injective := v.slots_injective
  low_main := v.low_main
  high_main := v.high_main
  low_anti := v.low_anti
  high_anti := v.high_anti

/-- Reuse every edge reservoir and gap certificate on the rebased pairs. -/
def centeredNetworkRebase {n : ℕ} {E K : Type*} [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a) (B : CenteredNetwork E K v)
    (c : Cell n ≃ Fin (n*n))
    (hfix : ∀ k side, entry c (rowNetworkSlot v (k,side)) = entry a (rowNetworkSlot v (k,side))) :
    CenteredNetwork E K (rowNetworkPairsRebase v c hfix) where
  block := B.block
  radius := B.radius
  source := B.source
  target := B.target
  disjoint := B.disjoint
  grid := B.grid
  endpoints := B.endpoints

/-- The midpoint's change is twice the ordinary row-sum change, because all
selected pair endpoints retain their actual values. -/
theorem physical_network_midpoint_completion_rebase {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a) (B : CenteredNetwork E K v)
    (c : Cell n ≃ Fin (n*n))
    (hfix : ∀ k side, entry c (rowNetworkSlot v (k,side)) = entry a (rowNetworkSlot v (k,side)))
    (r : Fin n) :
    physicalNetworkMidpointTwice (rowNetworkPairsRebase v c hfix)
        (centeredNetworkRebase v B c hfix) r - physicalNetworkMidpointTwice v B r =
      2 * ((rowSum c r : ℤ) - (rowSum a r : ℤ)) := by
  classical
  have hl (k : K) : entry c (v.low k, v.column k) = entry a (v.low k, v.column k) := by
    simpa [rowNetworkSlot] using hfix k false
  have hh (k : K) : entry c (v.high k, v.column k) = entry a (v.high k, v.column k) := by
    simpa [rowNetworkSlot] using hfix k true
  have hp (k : K) : physicalPairLineOriginal (rowNetworkPairsRebase v c hfix) k r =
      physicalPairLineOriginal v k r := by
    simp [physicalPairLineOriginal, rowNetworkPairsRebase, hl, hh]
  have hm (k : K) : physicalPairLineMidpointTwice (rowNetworkPairsRebase v c hfix) k r =
      physicalPairLineMidpointTwice v k r := by
    simp [physicalPairLineMidpointTwice, rowNetworkPairsRebase, hl, hh]
  simp only [physicalNetworkMidpointTwice, centeredNetworkRebase, hp, hm]
  ring

/-- Synchronizing an inactive-cell completion preserves the actual doubled
physical row-network invoice, on one newly constructed reference. -/
theorem physical_network_reference_completion_invoice {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    (a b c : Cell n ≃ Fin (n*n)) (active : Finset (Cell n))
    (v : RowNetworkPairs K a) (B : CenteredNetwork E K v)
    (hactive : ∀ x ∈ active, c x = a x)
    (hoff : ∀ x ∉ active, b x = a x)
    (himage : active.image b = active.image a)
    (hslots : ∀ k side, rowNetworkSlot v (k,side) ∈ active) :
    ∃ d : Cell n ≃ Fin (n*n),
      (∀ x ∈ active, d x = b x) ∧ (∀ x ∉ active, d x = c x) ∧
      ∃ hfix : ∀ k side, entry c (rowNetworkSlot v (k,side)) = entry a (rowNetworkSlot v (k,side)),
        ∀ r, 2 * (rowSum d r : ℤ) -
            physicalNetworkMidpointTwice (rowNetworkPairsRebase v c hfix)
              (centeredNetworkRebase v B c hfix) r =
          2 * (rowSum b r : ℤ) - physicalNetworkMidpointTwice v B r := by
  classical
  obtain ⟨d, hd, hdo⟩ := reference_completion_synchronise a b c active hactive hoff himage
  have hfix (k : K) (side : Bool) :
      entry c (rowNetworkSlot v (k,side)) = entry a (rowNetworkSlot v (k,side)) := by
    unfold entry
    rw [hactive _ (hslots k side)]
  refine ⟨d, hd, hdo, hfix, ?_⟩
  intro r
  have hraw : (∑ j : Fin n, ((entry d (r,j) : ℤ) - entry c (r,j))) =
      ∑ j : Fin n, ((entry b (r,j) : ℤ) - entry a (r,j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : (r,j) ∈ active
    · unfold entry
      rw [hd _ h, hactive _ h]
    · unfold entry
      rw [hdo _ h, hoff _ h]
      simp
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum] at hraw
  change (rowSum d r : ℤ) - (rowSum c r : ℤ) =
    (rowSum b r : ℤ) - (rowSum a r : ℤ) at hraw
  have hmid := physical_network_midpoint_completion_rebase v B c hfix r
  omega

/-- The same synchronized reference also preserves a column-network invoice.
Its slots are supplied in transposed coordinates and must lie in the original
active set after swapping their coordinates. -/
theorem physical_network_reference_completion_column_invoice {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    (a b c d : Cell n ≃ Fin (n*n)) (active : Finset (Cell n))
    (v : RowNetworkPairs K (LayerPacking.transposePlacement a)) (B : CenteredNetwork E K v)
    (hactive : ∀ x ∈ active, c x = a x)
    (href : ∀ x ∈ active, d x = b x)
    (hoff : ∀ x ∉ active, b x = a x)
    (hcomplete : ∀ x ∉ active, d x = c x)
    (hslots : ∀ k side, (rowNetworkSlot v (k,side)).swap ∈ active) :
    ∃ hfix : ∀ k side, entry (LayerPacking.transposePlacement c) (rowNetworkSlot v (k,side)) =
        entry (LayerPacking.transposePlacement a) (rowNetworkSlot v (k,side)),
      ∀ j, 2 * (columnSum d j : ℤ) -
          physicalNetworkMidpointTwice (rowNetworkPairsRebase v (LayerPacking.transposePlacement c) hfix)
            (centeredNetworkRebase v B (LayerPacking.transposePlacement c) hfix) j =
        2 * (columnSum b j : ℤ) - physicalNetworkMidpointTwice v B j := by
  classical
  have hfix (k : K) (side : Bool) :
      entry (LayerPacking.transposePlacement c) (rowNetworkSlot v (k,side)) =
        entry (LayerPacking.transposePlacement a) (rowNetworkSlot v (k,side)) := by
    unfold entry LayerPacking.transposePlacement
    change oddPrime (c (rowNetworkSlot v (k,side)).swap).val =
      oddPrime (a (rowNetworkSlot v (k,side)).swap).val
    rw [hactive _ (hslots k side)]
  refine ⟨hfix, ?_⟩
  intro j
  have hraw : (∑ i : Fin n, ((entry d (i,j) : ℤ) - entry c (i,j))) =
      ∑ i : Fin n, ((entry b (i,j) : ℤ) - entry a (i,j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : (i,j) ∈ active
    · unfold entry
      rw [href _ h, hactive _ h]
    · unfold entry
      rw [hcomplete _ h, hoff _ h]
      simp
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum] at hraw
  change (columnSum d j : ℤ) - (columnSum c j : ℤ) =
    (columnSum b j : ℤ) - (columnSum a j : ℤ) at hraw
  have hmid := physical_network_midpoint_completion_rebase v B (LayerPacking.transposePlacement c) hfix j
  simp only [LayerPacking.rowSum_transpose] at hmid
  omega

end
end Sude
