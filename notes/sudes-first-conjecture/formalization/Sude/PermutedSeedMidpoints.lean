import Sude.PermutedSeedExhaustive
import Sude.NarrowSeedStageMidpoints
import Sude.NarrowPoolValues

/-! Link the stage-permutation values to actual selected prime-pair midpoints. -/
namespace Sude
noncomputable section

/-- The selected group's sorted pair midpoint values. -/
def retainedStageMidpoint (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (j : Fin P) (i : Fin Q) : ℝ :=
  sortedSeedMidpoint candidates r Q gap hcard (retainedSeedStageIndex r P kept hsub hkept j) i

/-- Every actual permuted pair has precisely the corresponding permuted
selected-stage midpoint. -/
theorem permutedRetainedSeed_pair_midpoint {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (ω : Fin P → Equiv.Perm (Fin Q)) (j : Fin P) (i : Fin Q) :
    (((permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω ((j, i), false)).val : ℝ) +
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω ((j, i), true)).val) / 2 =
      retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j (ω j i) := by
  rfl

/-- The stage midpoint data lie in their actual sorted endpoint interval. -/
theorem retainedStageMidpoint_bounds {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hQ : 0 < Q) (j : Fin P) (i : Fin Q) :
    retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j i ∈
      Set.Icc (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩)
        (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩) := by
  have h := retainedSeedMidpoint_between candidates r P Q gap hcard kept hsub hkept initial hav hQ j i
  dsimp only at h ⊢
  push_cast at h
  simpa [retainedStageMidpoint, sortedSeedMidpoint, retainedSeedPoolValues, retainedSeedSlot] using h

/-- The stage interval width is exactly the source's sorted-group width. -/
theorem retainedStageMidpoint_range (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (hQ : 0 < Q) (j : Fin P) :
    retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
      retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩ =
    sortedSeedReal candidates r Q hcard ((retainedSeedStageIndex r P kept hsub hkept j).val * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard ((retainedSeedStageIndex r P kept hsub hkept j).val * Q) :=
  sortedSeedMidpoint_range candidates r Q gap hcard hQ (retainedSeedStageIndex r P kept hsub hkept j)

/-- Each physically placed rectangle pair has the midpoint selected by the
same stage permutation, including the reversed second pair. -/
theorem permutedSeed_placed_rectangle_midpoint {n r P Q gap d : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (ω : Fin P → Equiv.Perm (Fin Q)) (hdiag : (4 * d) * 2 ≤ Q)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin (P * (4 * d)) × Fin 4 → Cell n)
    (hplaced : ∀ x, entry a (cells x) =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        (prefixRectangleInput hdiag x)).val)
    (j : Fin P) (rect : Fin (4 * d)) (pair : Fin 2) :
    ((entry a (cells (finProdFinEquiv (j, rect), prefixPairCorner pair false)) : ℝ) +
      entry a (cells (finProdFinEquiv (j, rect), prefixPairCorner pair true))) / 2 =
      retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j
        (ω j (prefixDiagonalPairIndex hdiag (rect, pair))) := by
  rw [hplaced (finProdFinEquiv (j, rect), prefixPairCorner pair false),
    hplaced (finProdFinEquiv (j, rect), prefixPairCorner pair true),
    prefixRectangleInput_pair, prefixRectangleInput_pair]
  exact permutedRetainedSeed_pair_midpoint candidates r P Q gap hcard kept hsub hkept initial hav ω j _

/-- Each physically placed ordinary-network pair has the corresponding
permuted selected-stage midpoint. -/
theorem permutedSeed_placed_network_midpoint {n r P Q gap d layers m : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (ω : Fin P → Equiv.Perm (Fin Q)) (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q)
    (hlen : m = P * layers) (network : Fin 2) (a : Cell n ≃ Fin (n * n))
    (cells : Fin m × (Fin n × Bool) → Cell n)
    (hplaced : ∀ x, entry a (cells x) =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        (prefixNetworkInput hfit hlen network x)).val)
    (layer : Fin m) (edge : Fin n) :
    let p : Fin P × Fin layers := finProdFinEquiv.symm (Fin.cast hlen layer)
    ((entry a (cells (layer, (edge, false))) : ℝ) + entry a (cells (layer, (edge, true)))) / 2 =
      retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept p.1
        (ω p.1 (prefixOrdinaryPairIndex hfit (network, p.2, edge))) := by
  rw [hplaced (layer, (edge, false)), hplaced (layer, (edge, true))]
  simpa [prefixNetworkInput, prefixOrdinaryInput] using
    permutedRetainedSeed_pair_midpoint candidates r P Q gap hcard kept hsub hkept initial hav ω
      (finProdFinEquiv.symm (Fin.cast hlen layer) : Fin P × Fin layers).1
      (prefixOrdinaryPairIndex hfit (network,
        (finProdFinEquiv.symm (Fin.cast hlen layer) : Fin P × Fin layers).2, edge))

end
end Sude
