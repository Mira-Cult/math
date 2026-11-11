import Sude.DiagonalFullStockWidenedCompletion
import Sude.ReferenceCompletionEntryInputs

/-! Conditional same-witness diagonal placement, RF completion and fresh
physical row/column reference transport.  All analytic inputs are supplied;
no primality or later-flow claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000

/-- Join the widened-old DQ/RF witness with both physical network invoices.
The two completed squares agree outside the active set, and the same reference
retains both diagonal sums and both old midpoint-invoice errors. -/
theorem dq_rf_network_completion_join (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n r₀ bits : ℕ} {ER EC KR KC : Type*}
    [Fintype ER] [DecidableEq ER] [DecidableEq KR]
    [Fintype EC] [DecidableEq EC] [DecidableEq KC]
    (a b₀ : Cell n ≃ Fin (n*n)) (reserved active : Finset (Cell n))
    (ε : ℝ) (Dold : ℕ) (hε : 0 ≤ ε) (hn : 7 ≤ n) (hnmax : n ≤ 2^18)
    (hodd : Odd n) (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserve : 4 * reserved.card ≤ n*n)
    (hload : 4 * (r₀ + 6*bits + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6*bits+4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6*bits+4))
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n -
      3 * (poolMaximum n : ℝ) / (4*n))
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n +
      3 * (poolMaximum n : ℝ) / (4*n) ≤ poolMaximum n)
    (hdeleted : (apInterval
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n))
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n))
      2 1 ∩ reserved.image (entry a)).card ≤ Dold)
    (hgate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - (((Dold + (2*n - 1) : ℕ)) : ℝ))
    (vr : RowNetworkPairs KR a) (BR : CenteredNetwork ER KR vr)
    (vc : RowNetworkPairs KC (LayerPacking.transposePlacement a)) (BC : CenteredNetwork EC KC vc)
    (hsub : active ⊆ reserved)
    (hfixed : ∀ x ∉ active, entry b₀ x = entry a x)
    (himage : active.image (entry b₀) = active.image (entry a))
    (hmain : mainSum b₀ = mainSum a) (hanti : antiSum b₀ = antiSum a)
    (hrowSlots : ∀ k side, rowNetworkSlot vr (k,side) ∈ active)
    (hcolSlots : ∀ k side, (rowNetworkSlot vc (k,side)).swap ∈ active)
    (hinvrow : ∀ r, |2 * (rowSum b₀ r : ℤ) - physicalNetworkMidpointTwice vr BR r| ≤ 9)
    (hinvcol : ∀ j, |2 * (columnSum b₀ j : ℤ) - physicalNetworkMidpointTwice vc BC j| ≤ 9) :
    ∃ (diagonal c d : Cell n ≃ Fin (n*n)),
      (∀ z ∈ reserved, entry diagonal z = entry a z) ∧
      (∀ z ∈ reserved ∪ unreservedDiagonalCells reserved, entry c z = entry diagonal z) ∧
      (∀ z ∈ reserved, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
        ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
        ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      2*n ≤ (actualUnusedPool diagonal (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |centralEntriesMean (actualUnusedPool diagonal (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ 3 * (poolMaximum n : ℝ) / (4*n) ∧
      mainSum c = mainSum diagonal ∧ antiSum c = antiSum diagonal ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) ∧
      (∀ x ∈ active, entry d x = entry b₀ x) ∧ (∀ x ∉ active, entry d x = entry c x) ∧
      mainSum d = mainSum c ∧ antiSum d = antiSum c ∧
      ∃ hr : ∀ k side, entry c (rowNetworkSlot vr (k,side)) = entry a (rowNetworkSlot vr (k,side)),
      ∃ hc : ∀ k side, entry (LayerPacking.transposePlacement c) (rowNetworkSlot vc (k,side)) =
          entry (LayerPacking.transposePlacement a) (rowNetworkSlot vc (k,side)),
        (∀ r, |2 * (rowSum d r : ℤ) - physicalNetworkMidpointTwice (rowNetworkPairsRebase vr c hr)
            (centeredNetworkRebase vr BR c hr) r| ≤ 9) ∧
        (∀ j, |2 * (columnSum d j : ℤ) - physicalNetworkMidpointTwice
          (rowNetworkPairsRebase vc (LayerPacking.transposePlacement c) hc)
            (centeredNetworkRebase vc BC (LayerPacking.transposePlacement c) hc) j| ≤ 9) := by
  classical
  obtain ⟨diagonal, c, hdiagfix, hcdiagfix, hcfix, hmaindiag, hantidiag, hrow, hcol,
    hstock, hshift, hcmain, hcanti, hpool, hinject⟩ :=
    full_stock_dq_rf_from_widened_old bmor upper a reserved ε Dold hε hn hnmax hodd hcenter
      hreserve hload hrowlo hrowhi hcollo hcolhi hleft hright hdeleted hgate
  have hca : ∀ x ∈ active, entry c x = entry a x := fun x hx => hcfix x (hsub hx)
  obtain ⟨d, hd, hdo, hr, hc, hrows, hcols⟩ := physical_reference_completion_both_invoices
    a b₀ c active vr BR vc BC hca hfixed himage hrowSlots hcolSlots
  have hdiag := reference_completion_diagonal_sums a b₀ c d active hca hd hfixed hdo
  refine ⟨diagonal, c, d, hdiagfix, hcdiagfix, hcfix, hmaindiag, hantidiag, hrow, hcol,
    hstock, hshift, hcmain, hcanti, hpool, hinject, hd, hdo, hdiag.1 hmain, hdiag.2 hanti, hr, hc, ?_, ?_⟩
  · intro r
    rw [hrows r]
    exact hinvrow r
  · intro j
    rw [hcols j]
    exact hinvcol j

end
end Sude
