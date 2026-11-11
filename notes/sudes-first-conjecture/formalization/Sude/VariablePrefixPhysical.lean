import Sude.BTTracePoolValues
import Sude.PrefixPairAllocation

/-! Place variable-gap traced pairs in actual diagonal rectangle cells. -/
namespace Sude
noncomputable section

/-- The diagonal rectangle allocator works for any supplied stage gaps,
not only for the finite family of powers of two. -/
theorem install_variable_prefix_diagonal_rectangles {P d Q L n : ℕ}
    (hdiag : (4 * d) * 2 ≤ Q) (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (gaps : Fin P → ℕ) (values : (Fin P × Fin Q) × Bool → pool n)
    (hinj : Function.Injective values)
    (hgap : ∀ j i, (values ((j, i), true)).val = (values ((j, i), false)).val + gaps j)
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ reserved)
    (havoid : ∀ x c, c ∈ reserved → (values x).val ≠ entry a c) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (values (prefixRectangleInput hdiag x)).val) ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      (∀ t : Fin (P * (4 * d)),
        let j := (finProdFinEquiv.symm t : Fin P × Fin (4 * d)).1
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 1)) =
          entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 0)) + gaps j ∧
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 2)) =
          entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 3)) + gaps j) := by
  let cells : Fin (P * (4 * d)) × Fin 4 → Cell n := fun x =>
    packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)
  let v : Fin (P * (4 * d)) × Fin 4 → pool n := fun x => values (prefixRectangleInput hdiag x)
  have hc : Function.Injective cells := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have heq := packedRectangleCorner_injective hs choice h
    exact Prod.ext (Fin.castLE_injective hrect (congrArg (fun z : Fin L × Fin 4 => z.1) heq))
      (congrArg (fun z : Fin L × Fin 4 => z.2) heq)
  have hv : Function.Injective v := hinj.comp (prefixRectangleInput_injective hdiag)
  obtain ⟨b, hb, hfixed⟩ := place_distinct_pool_entries_preserving a cells v reserved
    hc hv hfree (fun x c hc' => havoid _ c hc')
  refine ⟨b, hb, hfixed, ?_⟩
  intro t
  have h₀ := hgap (finProdFinEquiv.symm t).1
    (prefixDiagonalPairIndex hdiag ((finProdFinEquiv.symm t).2, 0))
  have h₁ := hgap (finProdFinEquiv.symm t).1
    (prefixDiagonalPairIndex hdiag ((finProdFinEquiv.symm t).2, 1))
  constructor
  · rw [hb (t, 1), hb (t, 0)]
    simpa [v, prefixRectangleInput, prefixCornerCode] using h₀
  · rw [hb (t, 2), hb (t, 3)]
    simpa [v, prefixRectangleInput, prefixCornerCode] using h₁

/-- Install the actual traced matching values in the physical diagonal
rectangles, with their stage-specific gaps and all earlier cells fixed. -/
theorem BTStageTrace.install_diagonal_rectangles {g Q n : ℕ} {initial final : Finset ℕ} {R last : ℝ}
    {stages : List BTSelectedStage} (trace : BTStageTrace g Q initial R final last stages)
    {P d L : ℕ} (hlen : stages.length = P) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ reserved)
    (havoid : ∀ p ∈ initial, ∀ z ∈ reserved, p ≠ entry a z) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (trace.poolValues hlen hpool (prefixRectangleInput hdiag x)).val) ∧
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ t : Fin (P * (4 * d)),
        let j := (finProdFinEquiv.symm t : Fin P × Fin (4 * d)).1
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 1)) =
          entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 0)) +
            (BTStageTrace.stageAt stages hlen j).gap ∧
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 2)) =
          entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 3)) +
            (BTStageTrace.stageAt stages hlen j).gap) := by
  apply install_variable_prefix_diagonal_rectangles hdiag hrect hs choice
    (fun j => (BTStageTrace.stageAt stages hlen j).gap) (trace.poolValues hlen hpool)
    (trace.poolValues_injective hlen hpool) (trace.poolValues_gap hlen hpool) a reserved hfree
  intro ⟨⟨j, i⟩, side⟩ z hz
  exact havoid _ (trace.endpoint_mem_initial hlen j i side) z hz

/-- Stage-dependent gap assigned to every layer and edge in that stage. -/
def variablePrefixNetworkGap {P r m n : ℕ} (gaps : Fin P → ℕ)
    (hlen : m = P * r) (i : Fin m) (_edge : Fin n) : ℕ :=
  gaps ((finProdFinEquiv.symm (Fin.cast hlen i) : Fin P × Fin r).1)

theorem variable_prefixNetwork_pair_gap {P d r n Q m : ℕ}
    (gaps : Fin P → ℕ) (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q)
    (hlen : m = P * r) (network : Fin 2) (values : (Fin P × Fin Q) × Bool → pool n)
    (hgap : ∀ j i, (values ((j, i), true)).val = (values ((j, i), false)).val + gaps j)
    (i : Fin m) (edge : Fin n) :
    (values (prefixNetworkInput hfit hlen network (i, (edge, true)))).val =
      (values (prefixNetworkInput hfit hlen network (i, (edge, false)))).val +
        gaps ((finProdFinEquiv.symm (Fin.cast hlen i) : Fin P × Fin r).1) := hgap _ _

theorem install_variable_prefix_ordinary_networks {P d r n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (gaps : Fin P → ℕ) (values : (Fin P × Fin Q) × Bool → pool n) (hinj : Function.Injective values)
    (hgap : ∀ j i, (values ((j, i), true)).val =
      (values ((j, i), false)).val + gaps j)
    (initial : Finset ℕ) (havoid : ∀ x, (values x).val ∉ initial)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * r) (hclen : colPerms.length = P * r)
    (reserved : Finset (Cell n))
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (hrload : ∀ i, (LayerPacking.rowUsed reserved i).card ≤ L)
    (hcload : ∀ i, (LayerPacking.colUsed reserved i).card ≤ L)
    (hcapacity : 4 * (L + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n))
    (hreserved : ∀ c ∈ reserved, entry a c ∈ initial ∨
      ∃ y : Fin (P * (4 * d)) × Fin 4, entry a c = (values (prefixRectangleInput hdiag y)).val) :
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers reserved rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (reserved ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (values (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (values (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + variablePrefixNetworkGap gaps hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + variablePrefixNetworkGap gaps hclen (Fin.cast hcols i) e) ∧
      (∀ c ∈ reserved, entry b c = entry a c) := by
  let rv := fun x => values (prefixNetworkInput hfit hrlen 0 x)
  let cv := fun x => values (prefixNetworkInput hfit hclen 1 x)
  have hrv : Function.Injective rv := hinj.comp (prefixNetworkInput_injective hfit hrlen 0)
  have hcv : Function.Injective cv := hinj.comp (prefixNetworkInput_injective hfit hclen 1)
  have hsep : ∀ x y, (rv x).val ≠ (cv y).val := by
    intro x y h
    apply prefixNetworkInputs_separate hfit hrlen hclen x y
    apply hinj
    exact Subtype.ext h
  have hrav : ∀ x c, c ∈ reserved → (rv x).val ≠ entry a c := by
    intro x c hc h
    rcases hreserved c hc with hi | ⟨y, hy⟩
    · exact havoid _ (h ▸ hi)
    · apply prefixNetworkInput_ne_rectangle hfit hdiag hrlen 0 x y
      apply hinj
      exact Subtype.ext (h.trans hy)
  have hcav : ∀ x c, c ∈ reserved → (cv x).val ≠ entry a c := by
    intro x c hc h
    rcases hreserved c hc with hi | ⟨y, hy⟩
    · exact havoid _ (h ▸ hi)
    · apply prefixNetworkInput_ne_rectangle hfit hdiag hclen 1 x y
      apply hinj
      exact Subtype.ext (h.trans hy)
  obtain ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdisjoint,
    _, _, hrplaced, hcplaced, hrgap, hcgap, hfixed, _⟩ :=
    LayerPacking.pack_and_install_two_networks rowPerms colPerms reserved hrderange hcderange
      hrload hcload hcapacity a rv cv hrv hcv hsep hrav hcav
      (variablePrefixNetworkGap gaps hrlen) (variablePrefixNetworkGap gaps hclen)
      (variable_prefixNetwork_pair_gap gaps hfit hrlen 0 values hgap)
      (variable_prefixNetwork_pair_gap gaps hfit hclen 1 values hgap)
  exact ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdisjoint,
    hrplaced, hcplaced, hrgap, hcgap, hfixed⟩

/-- Place the FPF diagonal pairs and both ordinary pair networks in one
square. The retained population and numerical packing gates are inputs; all
cell and value separation between these families is proved here. -/
theorem install_variable_prefix_diagonal_and_ordinary {P d r n Q L B : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (gaps : Fin P → ℕ) (values : (Fin P × Fin Q) × Bool → pool n) (hinj : Function.Injective values)
    (hgap : ∀ j i, (values ((j, i), true)).val =
      (values ((j, i), false)).val + gaps j)
    (initial : Finset ℕ) (havoid : ∀ x, (values x).val ∉ initial)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * r) (hclen : colPerms.length = P * r)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ B)
    (hcapacity : 4 * ((B + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ base) :
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪
          LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (values (prefixRectangleInput hdiag x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (values (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (values (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + variablePrefixNetworkGap gaps hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + variablePrefixNetworkGap gaps hclen (Fin.cast hcols i) e) ∧
      (∀ c ∈ base, entry b c = entry a c) := by
  obtain ⟨a', hplaced, hbasefixed, _⟩ :=
    install_variable_prefix_diagonal_rectangles hdiag hrect hs choice gaps values hinj hgap a base hfree
      (by intro x c hc heq; exact havoid x (heq ▸ hbase c hc))
  let reserved := base ∪ allocatedBridgeRectangleSupport hrect hs choice
  have hres : ∀ c ∈ reserved, entry a' c ∈ initial ∨
      ∃ y : Fin (P * (4 * d)) × Fin 4, entry a' c = (values (prefixRectangleInput hdiag y)).val := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · left
      rw [hbasefixed c hc]
      exact hbase c hc
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
      right
      exact ⟨x, hplaced x⟩
  have hloads := allocatedBridgeReservation_load hrect hs choice base hrload hcload
  obtain ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpacked, hcpacked, hdisjoint,
    hrplaced, hcplaced, hrgap, hcgap, hfixed⟩ :=
    install_variable_prefix_ordinary_networks hfit hdiag gaps values hinj hgap initial havoid rowPerms colPerms
      hrlen hclen reserved hrderange hcderange hloads.1 hloads.2 hcapacity a' hres
  refine ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpacked, hcpacked, hdisjoint, ?_,
    hrplaced, hcplaced, hrgap, hcgap, ?_⟩
  · intro x
    have hx : packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∈ reserved := by
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨x, Finset.mem_univ _, rfl⟩
    rw [hfixed _ hx]
    exact hplaced x
  · intro c hc
    exact (hfixed c (Finset.mem_union_left _ hc)).trans (hbasefixed c hc)


/-- Install traced variable-gap pairs into both diagonal rectangles and two
ordinary physical networks, preserving the earlier reservation. All supplied
values come from the exact prescribed pool and no endpoint is reused. -/
theorem BTStageTrace.install_diagonal_and_ordinary {g Q n : ℕ} {traceInitial traceFinal : Finset ℕ}
    {R last : ℝ} {stages : List BTSelectedStage} (trace : BTStageTrace g Q traceInitial R traceFinal last stages)
    {P d r L B : ℕ} (hlen : stages.length = P)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (hpool : ∀ p ∈ traceInitial, p ∈ pool n) (prior : Finset ℕ)
    (havoid : ∀ p ∈ traceInitial, p ∉ prior)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * r) (hclen : colPerms.length = P * r)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ B)
    (hcapacity : 4 * ((B + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ prior)
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ base) :
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (trace.poolValues hlen hpool (prefixRectangleInput hdiag x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (trace.poolValues hlen hpool (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (trace.poolValues hlen hpool (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hlen j).gap) hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hlen j).gap) hclen (Fin.cast hcols i) e) ∧
      (∀ c ∈ base, entry b c = entry a c) := by
  have hav : ∀ x, (trace.poolValues hlen hpool x).val ∉ prior := by
    intro ⟨⟨j, i⟩, side⟩
    exact havoid _ (trace.endpoint_mem_initial hlen j i side)
  exact install_variable_prefix_diagonal_and_ordinary hfit hdiag hrect hs choice
    (fun j => (BTStageTrace.stageAt stages hlen j).gap) (trace.poolValues hlen hpool)
    (trace.poolValues_injective hlen hpool) (trace.poolValues_gap hlen hpool) prior hav
    rowPerms colPerms hrlen hclen hrderange hcderange base hrload hcload hcapacity a hbase hfree

end
end Sude
