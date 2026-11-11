import Sude.BridgePhysicalGrid
import Sude.NetworkPairJoin
import Sude.FamilyGrid

/-! Join an old physical grid to newly installed bridge pairs. -/
namespace Sude
noncomputable section

/-- Distinct within-stage edges get disjoint bridge labels; disjoint old
reservoirs therefore stay disjoint after all bridge stages are added. -/
theorem joinedBridgeGrid_disjoint {α : Type*} [DecidableEq α] {J r n m : ℕ}
    (hlen : m = J * r) (u v : Fin r × Fin n) (hne : u ≠ v)
    (initialU initialV : Finset α) (hdisjoint : Disjoint initialU initialV) :
    Disjoint
      (initialU.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.univ : Finset (Fin J)).image
          (fun j => Sum.inr (bridgeStageLayerIndex hlen j u.1, u.2)))
      (initialV.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.univ : Finset (Fin J)).image
          (fun j => Sum.inr (bridgeStageLayerIndex hlen j v.1, v.2))) := by
  apply Finset.disjoint_left.mpr
  intro z hzU hzV
  simp only [Finset.mem_union, Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hzU hzV
  rcases hzU with ⟨a, ha, rfl⟩ | ⟨i, hi⟩
  · rcases hzV with ⟨b, hb, hab⟩ | ⟨j, hj⟩
    · exact Finset.disjoint_left.mp hdisjoint ha (Sum.inl.inj hab ▸ hb)
    · cases hj
  · rcases hzV with ⟨b, hb, hbz⟩ | ⟨j, hj⟩
    · rw [← hi] at hbz
      cases hbz
    · have hp := Sum.inr.inj (hi.trans hj.symm)
      have hedge : u.2 = v.2 := congrArg (fun p : Fin m × Fin n => p.2) hp
      have hlayer := congrArg (fun p : Fin m × Fin n => p.1) hp
      have hpair := finProdFinEquiv.injective (Fin.cast_injective hlen.symm hlayer)
      have hwithin : u.1 = v.1 := congrArg Prod.snd hpair
      exact hne (Prod.ext hwithin hedge)

/-- The grown grid is on one actual pair system: the preserved initial
reservoir and the disjoint, newly packed bridge pairs. -/
theorem selectedBridgeBatches_joined_grid {α : Type*} [DecidableEq α]
    {J r n d k : ℕ} (reservedValues : Finset ℕ) (R₀ : ℝ)
    (batches : ℕ → List DoublePair) (hfit : 4 * d + r * n ≤ k)
    {a : Cell n ≃ Fin (n * n)} (old : RowNetworkPairs α a)
    (b : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hold : ∀ x, rowNetworkSlot old x ∈ reservedCells)
    (hfixed : ∀ c ∈ reservedCells, entry b c = entry a c)
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = J * r)
    (packed : LayerPacking.PackedLayers reservedCells layers)
    (hgap : ∀ i e, entry b ((layers.get i).1 e, (layers.get i).2 e) =
      entry b (e, (layers.get i).2 e) + bridgeNetworkGap hlen hfit batches i e)
    (layer : Fin r) (edge : Fin n) (initial : Finset α) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial old.gap radius) (hradius : 2 ∣ radius)
    (hcoverage : R₀ ≤ (radius : ℝ))
    (hbelow : ∀ j < J, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n)
    (hstop : (poolMaximum n : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ J)
    (hvalid : ∀ j < J,
      bridgeStageValid n reservedValues (bridgeIteration (poolMaximum n) R₀) batches k j) :
    let pairs := joinReservedPackedPairs old b reservedCells hold hfixed layers packed
      (bridgeNetworkGap hlen hfit batches) hgap
    CompleteEvenGrid
      (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.univ : Finset (Fin J)).image
          (fun j => Sum.inr (bridgeStageLayerIndex hlen j layer, edge)))
      pairs.gap
      (radius + ∑ j ∈ Finset.range J,
        selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (layer, edge)) j) ∧
      (poolMaximum n : ℝ) ≤
        ((radius + ∑ j ∈ Finset.range J,
          selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (layer, edge)) j : ℕ) : ℝ) := by
  have h := selectedBridgeBatches_packed_grid reservedValues R₀ batches hfit layers hlen
    reservedCells packed b hgap layer edge initial old.gap radius hgrid hradius hcoverage
    hbelow hstop hvalid
  simpa [joinReservedPackedPairs, RowNetworkPairs.join, RowNetworkPairs.rebase,
    LayerPacking.PackedLayers.rowPairs] using h

/-- If the old reservoir represents the same edge, every pair in the joined
grid has that edge's endpoints, including all stages of the physical bridge. -/
theorem joinedBridgeGrid_endpoints {α : Type*} [DecidableEq α] {J r n d k : ℕ}
    (batches : ℕ → List DoublePair) (hfit : 4 * d + r * n ≤ k)
    {a : Cell n ≃ Fin (n * n)} (old : RowNetworkPairs α a)
    (b : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hold : ∀ x, rowNetworkSlot old x ∈ reservedCells)
    (hfixed : ∀ c ∈ reservedCells, entry b c = entry a c)
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = J * r)
    (packed : LayerPacking.PackedLayers reservedCells layers)
    (hgap : ∀ i e, entry b ((layers.get i).1 e, (layers.get i).2 e) =
      entry b (e, (layers.get i).2 e) + bridgeNetworkGap hlen hfit batches i e)
    (perms : Fin r → Equiv.Perm (Fin n))
    (hperms : layers.map Prod.fst = bridgeRepeatedPermutations J perms)
    (layer : Fin r) (edge : Fin n) (initial : Finset α)
    (hends : ∀ x ∈ initial, old.low x = edge ∧ old.high x = perms layer edge) :
    let pairs := joinReservedPackedPairs old b reservedCells hold hfixed layers packed
      (bridgeNetworkGap hlen hfit batches) hgap
    ∀ x ∈ (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (Finset.univ : Finset (Fin J)).image
        (fun j => Sum.inr (bridgeStageLayerIndex hlen j layer, edge))),
      pairs.low x = edge ∧ pairs.high x = perms layer edge := by
  dsimp only
  intro x hx
  simp only [Finset.mem_union, Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ⟨z, hz, rfl⟩ | ⟨j, rfl⟩
  · simpa [joinReservedPackedPairs, RowNetworkPairs.join, RowNetworkPairs.rebase] using hends z hz
  · simpa [joinReservedPackedPairs, RowNetworkPairs.join,
      LayerPacking.PackedLayers.rowPairs] using
      (bridgePackedPair_endpoints batches hfit layers hlen perms hperms reservedCells packed b hgap
        j layer edge)

/-- Assemble all joined per-edge grids into the existing physical network
interface. Initial grids, their disjointness and their endpoints remain
explicit inputs; the bridge stages add no new cross-edge overlap. -/
def joinedBridgeCenteredNetwork {α : Type*} [DecidableEq α] {J r n d k : ℕ}
    (reservedValues : Finset ℕ) (R₀ : ℝ) (batches : ℕ → List DoublePair)
    (hfit : 4 * d + r * n ≤ k) {a : Cell n ≃ Fin (n * n)} (old : RowNetworkPairs α a)
    (b : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hold : ∀ x, rowNetworkSlot old x ∈ reservedCells)
    (hfixed : ∀ c ∈ reservedCells, entry b c = entry a c)
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = J * r)
    (packed : LayerPacking.PackedLayers reservedCells layers)
    (hgap : ∀ i e, entry b ((layers.get i).1 e, (layers.get i).2 e) =
      entry b (e, (layers.get i).2 e) + bridgeNetworkGap hlen hfit batches i e)
    (perms : Fin r → Equiv.Perm (Fin n))
    (hperms : layers.map Prod.fst = bridgeRepeatedPermutations J perms)
    (initial : Fin r × Fin n → Finset α) (radius : Fin r × Fin n → ℕ)
    (hdisjoint : ∀ e f, e ≠ f → Disjoint (initial e) (initial f))
    (hgrid : ∀ e, CompleteEvenGrid (initial e) old.gap (radius e))
    (heven : ∀ e, 2 ∣ radius e) (hcoverage : ∀ e, R₀ ≤ (radius e : ℝ))
    (hends : ∀ e x, x ∈ initial e → old.low x = e.2 ∧ old.high x = perms e.1 e.2)
    (hbelow : ∀ j < J, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n)
    (hstop : (poolMaximum n : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ J)
    (hvalid : ∀ j < J,
      bridgeStageValid n reservedValues (bridgeIteration (poolMaximum n) R₀) batches k j) :
    CenteredNetwork (Fin r × Fin n) (Sum α (Fin layers.length × Fin n))
      (joinReservedPackedPairs old b reservedCells hold hfixed layers packed
        (bridgeNetworkGap hlen hfit batches) hgap) where
  block := fun e => (initial e).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.univ : Finset (Fin J)).image
      (fun j => Sum.inr (bridgeStageLayerIndex hlen j e.1, e.2))
  radius := fun e => radius e + ∑ j ∈ Finset.range J,
    selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (e.1, e.2)) j
  source := Prod.snd
  target := fun e => perms e.1 e.2
  disjoint := fun e f h => joinedBridgeGrid_disjoint hlen e f h (initial e) (initial f) (hdisjoint e f h)
  grid := fun e => (selectedBridgeBatches_joined_grid reservedValues R₀ batches hfit old b
    reservedCells hold hfixed layers hlen packed hgap e.1 e.2 (initial e) (radius e)
    (hgrid e) (heven e) (hcoverage e) hbelow hstop hvalid).1
  endpoints := fun e => joinedBridgeGrid_endpoints batches hfit old b reservedCells hold hfixed
    layers hlen packed hgap perms hperms e.1 e.2 (initial e) (hends e)

theorem joinedBridgeCentered_radius_covers {α : Type*} [DecidableEq α] {J r n d k : ℕ}
    (reservedValues : Finset ℕ) (R₀ : ℝ) (batches : ℕ → List DoublePair)
    (hfit : 4 * d + r * n ≤ k) {a : Cell n ≃ Fin (n * n)} (old : RowNetworkPairs α a)
    (b : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hold : ∀ x, rowNetworkSlot old x ∈ reservedCells)
    (hfixed : ∀ c ∈ reservedCells, entry b c = entry a c)
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = J * r)
    (packed : LayerPacking.PackedLayers reservedCells layers)
    (hgap : ∀ i e, entry b ((layers.get i).1 e, (layers.get i).2 e) =
      entry b (e, (layers.get i).2 e) + bridgeNetworkGap hlen hfit batches i e)
    (layer : Fin r) (edge : Fin n) (initial : Finset α) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial old.gap radius) (heven : 2 ∣ radius)
    (hcoverage : R₀ ≤ (radius : ℝ))
    (hbelow : ∀ j < J, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n)
    (hstop : (poolMaximum n : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ J)
    (hvalid : ∀ j < J,
      bridgeStageValid n reservedValues (bridgeIteration (poolMaximum n) R₀) batches k j) :
    (poolMaximum n : ℝ) ≤
      ((radius + ∑ j ∈ Finset.range J,
        selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (layer, edge)) j : ℕ) : ℝ) :=
  (selectedBridgeBatches_joined_grid reservedValues R₀ batches hfit old b reservedCells hold hfixed
    layers hlen packed hgap layer edge initial radius hgrid heven hcoverage hbelow hstop hvalid).2

end
end Sude
