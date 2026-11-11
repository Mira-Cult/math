import Sude.FWPhysicalEdgeWitnessGrid
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- The installed sorted pair has gap two, independent of any availability
or reservation condition on the candidate endpoints. -/
theorem fw_seed_edge_gap_no_availability {n : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ x, entry grown (fwSeedOrdinaryCells sr sc hsr hsc x) =
      entry old (fwSeedOrdinaryCells sr sc hsr hsc x))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (edge : Fin 3 × Fin n) (network : Bool) (j : Fin 16) :
    entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j true) =
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j false) + 2 := by
  cases network
  · change entry grown (fwSeedOrdinaryCells sr sc hsr hsc (Sum.inl (finProdFinEquiv (j, edge.1), (edge.2, true)))) =
      entry grown (fwSeedOrdinaryCells sr sc hsr hsc (Sum.inl (finProdFinEquiv (j, edge.1), (edge.2, false)))) + 2
    rw [hfixed, hfixed, hso, hso]
    simp [fwSeedOrdinaryInput, prefixNetworkInput, prefixOrdinaryInput,
      retainedSeedSlot, sortedSeedEndpoint, pairEndpoint]
  · change entry grown (fwSeedOrdinaryCells sr sc hsr hsc (Sum.inr (finProdFinEquiv (j, edge.1), (edge.2, true)))) =
      entry grown (fwSeedOrdinaryCells sr sc hsr hsc (Sum.inr (finProdFinEquiv (j, edge.1), (edge.2, false)))) + 2
    rw [hfixed, hfixed, hso, hso]
    simp [fwSeedOrdinaryInput, prefixNetworkInput, prefixOrdinaryInput,
      retainedSeedSlot, sortedSeedEndpoint, pairEndpoint]
end
end Sude
