import Sude.BTGrowingPhysical
import Sude.PrefixAllocationCoverage

/-! Install a supplied growing trace at offset rectangles and supplied packed
layers, separating spatial geometry from the value-protected cells. No
packing existence, early-layout coverage, or crossing is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Consecutive rectangle labels after a supplied offset. -/
def btGrowingOffsetRectangle {P d L : ℕ} (offset : ℕ)
    (hfit : offset + P * (4 * d) ≤ L) (i : Fin (P * (4 * d))) : Fin L :=
  ⟨offset + i.val, by omega⟩

theorem btGrowingOffsetRectangle_injective {P d L : ℕ} (offset : ℕ)
    (hfit : offset + P * (4 * d) ≤ L) :
    Function.Injective (btGrowingOffsetRectangle (P := P) (d := d) offset hfit) := by
  intro x y h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [btGrowingOffsetRectangle] at hv
  omega

/-- Offset rectangles and supplied row/column layers for the same trace
allocation; column cells are transposed back to the original square. -/
def btGrowingOffsetCells {P d r n L : ℕ} (offset : ℕ)
    (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * r) (hc : cols.length = P * r) :
    PrefixPhysicalInputs P d r n → Cell n
  | Sum.inl x => packedRectangleCorner hs choice (btGrowingOffsetRectangle offset hoff x.1, x.2)
  | Sum.inr (Sum.inl x) => LayerPacking.sequenceCell rows (Fin.cast hr.symm x.1, x.2)
  | Sum.inr (Sum.inr x) => (LayerPacking.sequenceCell cols (Fin.cast hc.symm x.1, x.2)).swap

/-- The supplied packed layout makes every growth role cell distinct and
free of the value-protected cells. Full geometry may contain other cells,
whose old entries are not required to lie in the protected-value set. -/
theorem btGrowingOffsetCells_geometry {P d r n L : ℕ} (offset : ℕ)
    (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (base prior : Finset (Cell n)) (hrectbase : packedRectangleSupport hs choice ⊆ base)
    (hprior : prior ⊆ base)
    (hdiagfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (btGrowingOffsetRectangle offset hoff x.1, x.2) ∉ prior)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * r) (hc : cols.length = P * r)
    (hrows : LayerPacking.PackedLayers base rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) cols)
    (hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols))) :
    Function.Injective (btGrowingOffsetCells offset hoff hs choice rows cols hr hc) ∧
      (∀ x, btGrowingOffsetCells offset hoff hs choice rows cols hr hc x ∉ prior) := by
  have hrmem : ∀ x, LayerPacking.sequenceCell rows x ∈ LayerPacking.layersSupport rows := by
    intro x
    exact LayerPacking.layerSupport_subset (rows.get x.1) rows (List.get_mem rows x.1)
      (LayerPacking.sequenceCell_mem rows x.1 x.2)
  have hcmem : ∀ x, (LayerPacking.sequenceCell cols x).swap ∈
      LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
    intro x
    exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset (cols.get x.1) cols
      (List.get_mem cols x.1) (LayerPacking.sequenceCell_mem cols x.1 x.2), rfl⟩
  have hrfree : ∀ x, LayerPacking.sequenceCell rows x ∉ base := fun x => hrows.sequenceCell_unreserved x
  have hcfree : ∀ x, (LayerPacking.sequenceCell cols x).swap ∉ base := by
    intro x hx
    exact (hcols.transposed_support_safe _ (hcmem x)).1 (Finset.mem_union_left _ hx)
  have hdmem : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (btGrowingOffsetRectangle offset hoff x.1, x.2) ∈ base := by
    intro x
    apply hrectbase
    exact Finset.mem_image.mpr ⟨(btGrowingOffsetRectangle offset hoff x.1, x.2), Finset.mem_univ _, rfl⟩
  have hdiagInj : Function.Injective (fun x : Fin (P * (4 * d)) × Fin 4 =>
      packedRectangleCorner hs choice (btGrowingOffsetRectangle offset hoff x.1, x.2)) := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have heq := packedRectangleCorner_injective hs choice h
    exact Prod.ext (btGrowingOffsetRectangle_injective offset hoff
      (congrArg (fun z : Fin L × Fin 4 => z.1) heq))
      (congrArg (fun z : Fin L × Fin 4 => z.2) heq)
  constructor
  · intro x y heq
    rcases x with x | (x | x) <;> rcases y with y | (y | y) <;>
      dsimp only [btGrowingOffsetCells] at heq
    · exact congrArg Sum.inl (hdiagInj heq)
    · exact False.elim (hrfree _ (heq ▸ hdmem _))
    · exact False.elim (hcfree _ (heq ▸ hdmem _))
    · exact False.elim (hrfree _ (heq ▸ hdmem _))
    · apply congrArg (Sum.inr ∘ Sum.inl)
      have h := hrows.sequenceCell_injective heq
      exact Prod.ext (Fin.cast_injective hr.symm (congrArg Prod.fst h))
        (congrArg (fun z : Fin rows.length × (Fin n × Bool) => z.2) h)
    · exact False.elim (Finset.disjoint_left.mp hdisjoint (hrmem _) (heq ▸ hcmem _))
    · exact False.elim (hcfree _ (heq ▸ hdmem _))
    · exact False.elim (Finset.disjoint_left.mp hdisjoint (heq ▸ hrmem _) (hcmem _))
    · apply congrArg (Sum.inr ∘ Sum.inr)
      have heq' := congrArg Prod.swap heq
      simp only [Prod.swap_swap] at heq'
      have h := hcols.sequenceCell_injective heq'
      exact Prod.ext (Fin.cast_injective hc.symm (congrArg Prod.fst h))
        (congrArg (fun z : Fin cols.length × (Fin n × Bool) => z.2) h)
  · intro x
    rcases x with x | (x | x)
    · exact hdiagfree x
    · intro hx
      exact hrfree _ (hprior hx)
    · intro hx
      exact hcfree _ (hprior hx)

/-- Install all physical roles of the exact supplied trace at once. Row and
column layers and the free offset rectangles are hypotheses; protected cells
are preserved while unrelated values in `base` may change. -/
theorem BTGrowingTrace.install_offset_roles {g Q n : ℕ} {initial final : Finset ℕ}
    {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial R final last stages) {P d r L : ℕ}
    (hlen : stages.length = P) (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q)
    (hdiag : (4 * d) * 2 ≤ Q) (offset : ℕ) (hoff : offset + P * (4 * d) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (hpool : ∀ p ∈ initial, p ∈ pool n) (removed : Finset ℕ)
    (havoid : ∀ p ∈ initial, p ∉ removed)
    (a : Cell n ≃ Fin (n*n)) (base prior : Finset (Cell n))
    (hrectbase : packedRectangleSupport hs choice ⊆ base) (hprior : prior ⊆ base)
    (hpriorValues : ∀ c ∈ prior, entry a c ∈ removed)
    (hdiagfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (btGrowingOffsetRectangle offset hoff x.1, x.2) ∉ prior)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * r) (hc : cols.length = P * r)
    (hrows : LayerPacking.PackedLayers base rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) cols)
    (hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols))) :
    ∃ b : Cell n ≃ Fin (n*n),
      (∀ x : PrefixPhysicalInputs P d r n,
        entry b (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
          (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ c ∈ prior, entry b c = entry a c) ∧
      (∀ (j : Fin P) (u : Fin (4 * d)) (pair : Fin 2),
        entry b (btGrowingOffsetCells offset hoff hs choice rows cols hr hc
          (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair true))) =
        entry b (btGrowingOffsetCells offset hoff hs choice rows cols hr hc
          (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair false))) +
            (BTStageTrace.stageAt stages hlen j).gap) ∧
      (∀ (i : Fin (P * r)) (e : Fin n),
        entry b (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inl (i, (e, true))))) =
        entry b (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inl (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hlen j).gap) rfl i e) ∧
      (∀ (i : Fin (P * r)) (e : Fin n),
        entry b (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inr (i, (e, true))))) =
        entry b (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inr (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hlen j).gap) rfl i e) ∧
      ((4 * d) * 2 + 2 * (r * n) = Q →
        ∀ y : (Fin P × Fin Q) × Bool, ∃ x : PrefixPhysicalInputs P d r n,
          prefixPhysicalInput hfit hdiag x = y ∧
          entry b (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
            (trace.poolValues hlen hpool y).val) := by
  let cells := btGrowingOffsetCells offset hoff hs choice rows cols hr hc
  let values := fun x => trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)
  obtain ⟨hcells, hfree⟩ := btGrowingOffsetCells_geometry offset hoff hs choice base prior hrectbase hprior
    hdiagfree rows cols hr hc hrows hcols hdisjoint
  have hvalues : Function.Injective values :=
    (trace.poolValues_injective hlen hpool).comp (prefixPhysicalInput_injective hfit hdiag)
  have hav : ∀ x c, c ∈ prior → (values x).val ≠ entry a c := by
    intro x c hc heq
    have hv : (values x).val ∈ initial := by
      change (if (prefixPhysicalInput hfit hdiag x).2 then
        trace.lowAt hlen (prefixPhysicalInput hfit hdiag x).1.1 (prefixPhysicalInput hfit hdiag x).1.2 +
          (BTStageTrace.stageAt stages hlen (prefixPhysicalInput hfit hdiag x).1.1).gap
        else trace.lowAt hlen (prefixPhysicalInput hfit hdiag x).1.1 (prefixPhysicalInput hfit hdiag x).1.2) ∈ initial
      exact trace.endpoint_mem_initial hlen _ _ _
    exact havoid _ hv (heq ▸ hpriorValues c hc)
  obtain ⟨b, hplaced, hfixed⟩ :=
    place_distinct_pool_entries_preserving a cells values prior hcells hvalues hfree hav
  refine ⟨b, hplaced, hfixed, ?_, ?_, ?_, ?_⟩
  · intro j u pair
    rw [hplaced (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair true)),
      hplaced (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair false))]
    change (trace.poolValues hlen hpool (prefixRectangleInput hdiag
      (finProdFinEquiv (j, u), prefixPairCorner pair true))).val =
      (trace.poolValues hlen hpool (prefixRectangleInput hdiag
        (finProdFinEquiv (j, u), prefixPairCorner pair false))).val + _
    rw [prefixRectangleInput_pair, prefixRectangleInput_pair]
    exact trace.poolValues_gap hlen hpool j (prefixDiagonalPairIndex hdiag (u, pair))
  · intro i e
    rw [hplaced (Sum.inr (Sum.inl (i, (e, true)))), hplaced (Sum.inr (Sum.inl (i, (e, false))))]
    exact variable_prefixNetwork_pair_gap _ hfit rfl 0 _ (trace.poolValues_gap hlen hpool) i e
  · intro i e
    rw [hplaced (Sum.inr (Sum.inr (i, (e, true)))), hplaced (Sum.inr (Sum.inr (i, (e, false))))]
    exact variable_prefixNetwork_pair_gap _ hfit rfl 1 _ (trace.poolValues_gap hlen hpool) i e
  · intro hexact y
    obtain ⟨x, hx⟩ := (prefixPhysicalInput_bijective hfit hdiag hexact).2 y
    refine ⟨x, hx, ?_⟩
    exact (hplaced x).trans (congrArg (fun z => (trace.poolValues hlen hpool z).val) hx)

end
end Sude
