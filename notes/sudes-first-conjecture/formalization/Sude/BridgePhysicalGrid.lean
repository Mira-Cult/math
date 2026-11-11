import Sude.BridgeOrdinaryNetworks
import Sude.NetworkSwitches

/-! Transport bridge grids onto the finite labels of physically placed pairs. -/
namespace Sude
noncomputable section

/-- A complete grid survives an injective relabelling of its finite support.
No injection from the entire ambient type is required. -/
theorem completeEvenGrid_finite_relabel {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (gap : α → ℕ) (radius : ℕ)
    (f : {x // x ∈ S} → β) (hf : Function.Injective f) (newGap : β → ℕ)
    (hgap : ∀ x, newGap (f x) = gap x.val)
    (hgrid : CompleteEvenGrid S gap radius) :
    CompleteEvenGrid (S.attach.image f) newGap radius := by
  intro t ht heven
  obtain ⟨T, hT, hsum⟩ := hgrid t ht heven
  let g : {x // x ∈ T} → β := fun x => f ⟨x.val, hT x.property⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x // x ∈ S} => z.val) (hf h)
  refine ⟨T.attach.image g, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨⟨x.val, hT x.property⟩, by simp, rfl⟩
  · rw [Finset.sum_image (fun x _ y _ h => hg h)]
    simpa [g, hgap, Finset.sum_attach] using hsum

/-- The actual layer used for a particular stage and within-stage layer. -/
def bridgeStageLayerIndex {J r m : ℕ} (hlen : m = J * r)
    (stage : Fin J) (layer : Fin r) : Fin m :=
  Fin.cast hlen.symm (finProdFinEquiv (stage, layer))

theorem bridgeStageLayerIndex_injective {J r m : ℕ} (hlen : m = J * r)
    (layer : Fin r) : Function.Injective (fun stage => bridgeStageLayerIndex hlen stage layer) := by
  intro a b h
  apply Fin.ext
  have h' := congrArg (fun x : Fin m => finProdFinEquiv.symm (Fin.cast hlen x)) h
  simpa [bridgeStageLayerIndex] using congrArg (fun x : Fin J × Fin r => x.1.val) h'

theorem bridgeNetworkGap_stage {J r n d k m : ℕ} (hlen : m = J * r)
    (hfit : 4 * d + r * n ≤ k) (batches : ℕ → List DoublePair)
    (stage : Fin J) (layer : Fin r) (edge : Fin n) :
    bridgeNetworkGap hlen hfit batches (bridgeStageLayerIndex hlen stage layer) edge =
      selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (layer, edge)) stage := by
  simp [bridgeNetworkGap, bridgeStageLayerIndex]

theorem bridgeNetworkGap_cast {J r n d k m q : ℕ} (h₁ : m = q) (h₂ : q = J * r)
    (hfit : 4 * d + r * n ≤ k) (batches : ℕ → List DoublePair)
    (layer : Fin m) (edge : Fin n) :
    bridgeNetworkGap h₂ hfit batches (Fin.cast h₁ layer) edge =
      bridgeNetworkGap (h₁.trans h₂) hfit batches layer edge := by
  simp [bridgeNetworkGap]

/-- Repeat the same finite family of graph permutations at every bridge
stage, in precisely the order used by the physical layer indices. -/
def bridgeRepeatedPermutations {r n : ℕ} (J : ℕ) (perms : Fin r → Equiv.Perm (Fin n)) :
    List (Equiv.Perm (Fin n)) :=
  List.ofFn (fun i : Fin (J * r) => perms (finProdFinEquiv.symm i).2)

theorem bridgeRepeatedPermutations_length {J r n : ℕ} (perms : Fin r → Equiv.Perm (Fin n)) :
    (bridgeRepeatedPermutations J perms).length = J * r := by
  simp [bridgeRepeatedPermutations]

theorem bridgeRepeatedPermutations_derange {J r n : ℕ} (perms : Fin r → Equiv.Perm (Fin n))
    (hderange : ∀ l e, perms l e ≠ e) :
    ∀ π ∈ bridgeRepeatedPermutations J perms, ∀ e, π e ≠ e := by
  intro π hπ e
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hπ
  exact hderange (finProdFinEquiv.symm i).2 e

/-- When the installed permutations repeat stage by stage, every indexed
pair on the same within-stage edge has the same graph endpoints. -/
theorem bridgeStageLayer_endpoints {J r n : ℕ} (layers : List (LayerPacking.Layer n))
    (hlen : layers.length = J * r) (perms : Fin r → Equiv.Perm (Fin n))
    (hperms : layers.map Prod.fst = bridgeRepeatedPermutations J perms)
    (j : Fin J) (layer : Fin r) (edge : Fin n) :
    (layers.get (bridgeStageLayerIndex hlen j layer)).1 edge = perms layer edge := by
  have hidx : (bridgeStageLayerIndex hlen j layer).val <
      (bridgeRepeatedPermutations J perms).length := by
    rw [bridgeRepeatedPermutations_length]
    exact (Fin.cast hlen (bridgeStageLayerIndex hlen j layer)).isLt
  have hget := congrArg (fun xs : List (Equiv.Perm (Fin n)) => xs[(bridgeStageLayerIndex hlen j layer).val]?) hperms
  have hl := (bridgeStageLayerIndex hlen j layer).isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hidx, Option.map_some,
    Option.some.injEq] at hget
  simp only [bridgeRepeatedPermutations, List.getElem_ofFn] at hget
  change (layers.get (bridgeStageLayerIndex hlen j layer)).1 =
    perms (finProdFinEquiv.symm (Fin.cast hlen (bridgeStageLayerIndex hlen j layer))).2 at hget
  simpa [bridgeStageLayerIndex] using congrArg (fun p : Equiv.Perm (Fin n) => p edge) hget

def bridgeAbstractSupport {α : Type*} [DecidableEq α] (initial : Finset α) (J : ℕ) :
    Finset (Sum α ℕ) :=
  initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.range J).image (Sum.inr : ℕ → Sum α ℕ)

/-- Each abstract stage is mapped to its actual finite layer/edge label;
initial labels remain on the separate left side of the sum. -/
def bridgePhysicalLabel {α : Type*} [DecidableEq α] {J r n m : ℕ}
    (initial : Finset α) (hlen : m = J * r) (layer : Fin r) (edge : Fin n)
    (x : {x // x ∈ bridgeAbstractSupport initial J}) : Sum α (Fin m × Fin n) :=
  match x with
  | ⟨.inl a, _⟩ => .inl a
  | ⟨.inr j, hj⟩ => .inr (bridgeStageLayerIndex hlen ⟨j, by
      simpa [bridgeAbstractSupport] using hj⟩ layer, edge)

theorem bridgePhysicalLabel_injective {α : Type*} [DecidableEq α] {J r n m : ℕ}
    (initial : Finset α) (hlen : m = J * r) (layer : Fin r) (edge : Fin n) :
    Function.Injective (bridgePhysicalLabel initial hlen layer edge) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  apply Subtype.ext
  cases a with
  | inl a =>
    cases b with
    | inl b => simpa [bridgePhysicalLabel] using h
    | inr b => simp [bridgePhysicalLabel] at h
  | inr a =>
    cases b with
    | inl b => simp [bridgePhysicalLabel] at h
    | inr b =>
      have heq := congrArg Prod.fst (Sum.inr.inj h)
      have hab := bridgeStageLayerIndex_injective hlen layer heq
      exact congrArg Sum.inr (congrArg Fin.val hab)

/-- The finite support consists exactly of the initial labels and one
physically indexed edge per bridge stage. -/
theorem bridgePhysicalLabel_support {α : Type*} [DecidableEq α] {J r n m : ℕ}
    (initial : Finset α) (hlen : m = J * r) (layer : Fin r) (edge : Fin n) :
    (bridgeAbstractSupport initial J).attach.image (bridgePhysicalLabel initial hlen layer edge) =
      initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.univ : Finset (Fin J)).image
          (fun j => Sum.inr (bridgeStageLayerIndex hlen j layer, edge)) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Finset.mem_union,
    Finset.mem_map, Finset.mem_univ]
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    cases x with
    | inl a =>
      left
      have ha : a ∈ initial := by simpa [bridgeAbstractSupport] using hx
      exact ⟨a, ha, rfl⟩
    | inr j =>
      right
      have hj : j < J := by simpa [bridgeAbstractSupport] using hx
      exact ⟨⟨j, hj⟩, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨⟨Sum.inl a, ?_⟩, rfl⟩
      simp [bridgeAbstractSupport, ha]
    · refine ⟨⟨Sum.inr j.val, ?_⟩, ?_⟩
      · simp [bridgeAbstractSupport, j.isLt]
      · rfl

/-- An initial grid and the selected bridge gaps form a grid on the actual
finite layer/edge labels used by the ordinary network installation. -/
theorem selectedBridgeBatches_physical_grid {α : Type*} [DecidableEq α]
    {J r n d k m : ℕ} (reserved : Finset ℕ) (R₀ : ℝ)
    (batches : ℕ → List DoublePair) (hlen : m = J * r)
    (hfit : 4 * d + r * n ≤ k) (layer : Fin r) (edge : Fin n)
    (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial initialGap radius) (hradius : 2 ∣ radius)
    (hcoverage : R₀ ≤ (radius : ℝ))
    (hbelow : ∀ j < J, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n)
    (hstop : (poolMaximum n : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ J)
    (hvalid : ∀ j < J,
      bridgeStageValid n reserved (bridgeIteration (poolMaximum n) R₀) batches k j) :
    CompleteEvenGrid
      ((bridgeAbstractSupport initial J).attach.image
        (bridgePhysicalLabel initial hlen layer edge))
      (Sum.elim initialGap (fun p => bridgeNetworkGap hlen hfit batches p.1 p.2))
      (radius + ∑ j ∈ Finset.range J,
        selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (layer, edge)) j) ∧
      (poolMaximum n : ℝ) ≤
        ((radius + ∑ j ∈ Finset.range J,
          selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (layer, edge)) j : ℕ) : ℝ) := by
  let index := bridgeOrdinaryBlockIndex hfit (layer, edge)
  have h := selectedBridgeBatches_grow_grid n reserved R₀ batches k J index initial initialGap
    radius hgrid hradius hcoverage hbelow hstop hvalid
  refine ⟨completeEvenGrid_finite_relabel (bridgeAbstractSupport initial J)
    (joinedBridgeGap initialGap batches index) _ (bridgePhysicalLabel initial hlen layer edge)
    (bridgePhysicalLabel_injective initial hlen layer edge) _ ?_ h.1, h.2⟩
  rintro ⟨x, hx⟩
  cases x with
  | inl a => rfl
  | inr j =>
    simp [bridgePhysicalLabel, joinedBridgeGap, index, bridgeNetworkGap_stage]

/-- The physical grid uses the gaps in a packed row-network pair system.
The same statement applies to packed column layers in the transposed square. -/
theorem selectedBridgeBatches_packed_grid {α : Type*} [DecidableEq α]
    {J r n d k : ℕ} (reservedValues : Finset ℕ) (R₀ : ℝ)
    (batches : ℕ → List DoublePair) (hfit : 4 * d + r * n ≤ k)
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = J * r)
    (reservedCells : Finset (Cell n)) (packed : LayerPacking.PackedLayers reservedCells layers)
    (a : Cell n ≃ Fin (n * n))
    (hgap : ∀ i e, entry a ((layers.get i).1 e, (layers.get i).2 e) =
      entry a (e, (layers.get i).2 e) + bridgeNetworkGap hlen hfit batches i e)
    (layer : Fin r) (edge : Fin n) (initial : Finset α) (initialGap : α → ℕ)
    (radius : ℕ) (hgrid : CompleteEvenGrid initial initialGap radius) (hradius : 2 ∣ radius)
    (hcoverage : R₀ ≤ (radius : ℝ))
    (hbelow : ∀ j < J, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n)
    (hstop : (poolMaximum n : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ J)
    (hvalid : ∀ j < J,
      bridgeStageValid n reservedValues (bridgeIteration (poolMaximum n) R₀) batches k j) :
    CompleteEvenGrid
      (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.univ : Finset (Fin J)).image
          (fun j => Sum.inr (bridgeStageLayerIndex hlen j layer, edge)))
      (Sum.elim initialGap (packed.rowPairs a (bridgeNetworkGap hlen hfit batches) hgap).gap)
      (radius + ∑ j ∈ Finset.range J,
        selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (layer, edge)) j) ∧
      (poolMaximum n : ℝ) ≤
        ((radius + ∑ j ∈ Finset.range J,
          selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (layer, edge)) j : ℕ) : ℝ) := by
  have h := selectedBridgeBatches_physical_grid reservedValues R₀ batches hlen hfit layer edge
    initial initialGap radius hgrid hradius hcoverage hbelow hstop hvalid
  simpa only [bridgePhysicalLabel_support, LayerPacking.PackedLayers.rowPairs] using h

theorem bridgePackedPair_endpoints {J r n d k : ℕ}
    (batches : ℕ → List DoublePair) (hfit : 4 * d + r * n ≤ k)
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = J * r)
    (perms : Fin r → Equiv.Perm (Fin n))
    (hperms : layers.map Prod.fst = bridgeRepeatedPermutations J perms)
    (reservedCells : Finset (Cell n)) (packed : LayerPacking.PackedLayers reservedCells layers)
    (a : Cell n ≃ Fin (n * n))
    (hgap : ∀ i e, entry a ((layers.get i).1 e, (layers.get i).2 e) =
      entry a (e, (layers.get i).2 e) + bridgeNetworkGap hlen hfit batches i e)
    (j : Fin J) (layer : Fin r) (edge : Fin n) :
    let pairs := packed.rowPairs a (bridgeNetworkGap hlen hfit batches) hgap
    pairs.low (bridgeStageLayerIndex hlen j layer, edge) = edge ∧
      pairs.high (bridgeStageLayerIndex hlen j layer, edge) = perms layer edge := by
  exact ⟨rfl, bridgeStageLayer_endpoints layers hlen perms hperms j layer edge⟩

end
end Sude
