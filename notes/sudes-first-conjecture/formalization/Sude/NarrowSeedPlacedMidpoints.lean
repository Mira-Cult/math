import Sude.NarrowSeedStageMidpoints
import Sude.NarrowPoolValues

/-! Midpoint ranges in physically installed narrowed seed networks. -/
namespace Sude
noncomputable section

/-- Ordinary network pairs in the same installed stage use actual selected
values whose midpoint spread is bounded by that group's source width. -/
theorem retainedSeed_network_midpoints {n r P Q gap d layers m : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hQ : 0 < Q) (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q)
    (hlen : m = P * layers) (network : Fin 2) (layer : Fin m) (e f : Fin n) :
    let values := retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav
    let stage := (finProdFinEquiv.symm (Fin.cast hlen layer) : Fin P × Fin layers).1
    let group := retainedSeedStageIndex r P kept hsub hkept stage
    |(((values (prefixNetworkInput hfit hlen network (layer, (e, false)))).val : ℝ) +
        (values (prefixNetworkInput hfit hlen network (layer, (e, true)))).val) / 2 -
      (((values (prefixNetworkInput hfit hlen network (layer, (f, false)))).val : ℝ) +
        (values (prefixNetworkInput hfit hlen network (layer, (f, true)))).val) / 2| ≤
      sortedSeedReal candidates r Q hcard (group.val * Q + (Q - 1)) -
        sortedSeedReal candidates r Q hcard (group.val * Q) := by
  let p : Fin P × Fin layers := finProdFinEquiv.symm (Fin.cast hlen layer)
  have h := retainedSeedMidpoint_spread candidates r P Q gap hcard kept hsub hkept initial hav hQ p.1
    (prefixOrdinaryPairIndex hfit (network, p.2, e))
    (prefixOrdinaryPairIndex hfit (network, p.2, f))
  simpa [prefixNetworkInput, prefixOrdinaryInput, p] using h

/-- The previous bound holds for the actual entries of any square satisfying
the allocator's network placement equations. -/
theorem retainedSeed_placed_network_midpoints {n r P Q gap d layers m : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hQ : 0 < Q) (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q)
    (hlen : m = P * layers) (network : Fin 2) (a : Cell n ≃ Fin (n * n))
    (cells : Fin m × (Fin n × Bool) → Cell n)
    (hplaced : ∀ x, entry a (cells x) =
      (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav
        (prefixNetworkInput hfit hlen network x)).val)
    (layer : Fin m) (e f : Fin n) :
    let stage := (finProdFinEquiv.symm (Fin.cast hlen layer) : Fin P × Fin layers).1
    let group := retainedSeedStageIndex r P kept hsub hkept stage
    |((entry a (cells (layer, (e, false))) : ℝ) + entry a (cells (layer, (e, true)))) / 2 -
      ((entry a (cells (layer, (f, false))) : ℝ) + entry a (cells (layer, (f, true)))) / 2| ≤
      sortedSeedReal candidates r Q hcard (group.val * Q + (Q - 1)) -
        sortedSeedReal candidates r Q hcard (group.val * Q) := by
  simp only [hplaced]
  exact retainedSeed_network_midpoints candidates hcard kept hsub hkept initial hav hQ hfit hlen network layer e f

/-- Both rectangle pairs, including the reversed second pair, inherit the
same actual selected-stage midpoint range after placement. -/
theorem retainedSeed_placed_rectangle_midpoints {n r P Q gap d : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hQ : 0 < Q) (hdiag : (4 * d) * 2 ≤ Q) (a : Cell n ≃ Fin (n * n))
    (cells : Fin (P * (4 * d)) × Fin 4 → Cell n)
    (hplaced : ∀ x, entry a (cells x) =
      (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav
        (prefixRectangleInput hdiag x)).val)
    (j : Fin P) (u v : Fin (4 * d)) (p q : Fin 2) :
    let group := retainedSeedStageIndex r P kept hsub hkept j
    |((entry a (cells (finProdFinEquiv (j, u), prefixPairCorner p false)) : ℝ) +
        entry a (cells (finProdFinEquiv (j, u), prefixPairCorner p true))) / 2 -
      ((entry a (cells (finProdFinEquiv (j, v), prefixPairCorner q false)) : ℝ) +
        entry a (cells (finProdFinEquiv (j, v), prefixPairCorner q true))) / 2| ≤
      sortedSeedReal candidates r Q hcard (group.val * Q + (Q - 1)) -
        sortedSeedReal candidates r Q hcard (group.val * Q) := by
  simp only [hplaced, prefixRectangleInput_pair]
  exact retainedSeedMidpoint_spread candidates r P Q gap hcard kept hsub hkept initial hav hQ j
    (prefixDiagonalPairIndex hdiag (u, p)) (prefixDiagonalPairIndex hdiag (v, q))

end
end Sude
