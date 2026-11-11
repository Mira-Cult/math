import Sude.BridgeNetworkAfterRectangles

/-! Allocate one retained FPF prefix population without duplicating pairs. -/
namespace Sude
noncomputable section

/-- Each stage first uses two single pairs for each diagonal rectangle. -/
def prefixDiagonalPairIndex {d Q : ℕ} (hfit : (4 * d) * 2 ≤ Q)
    (x : Fin (4 * d) × Fin 2) : Fin Q :=
  Fin.castLE hfit (finProdFinEquiv x)

theorem prefixDiagonalPairIndex_injective {d Q : ℕ} (hfit : (4 * d) * 2 ≤ Q) :
    Function.Injective (prefixDiagonalPairIndex hfit) := by
  intro x y h
  exact finProdFinEquiv.injective (Fin.castLE_injective hfit h)

/-- The remaining pairs supply the row and column networks, independently. -/
def prefixOrdinaryPairIndex {d r n Q : ℕ} (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q)
    (x : Fin 2 × (Fin r × Fin n)) : Fin Q :=
  ⟨(4 * d) * 2 + (finProdFinEquiv (x.1, finProdFinEquiv x.2)).val, by
    have h := (finProdFinEquiv (x.1, finProdFinEquiv x.2)).isLt
    omega⟩

theorem prefixOrdinaryPairIndex_injective {d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) :
    Function.Injective (prefixOrdinaryPairIndex hfit) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have heq : finProdFinEquiv (a, finProdFinEquiv x) =
      finProdFinEquiv (b, finProdFinEquiv y) := by
    apply Fin.ext
    have h' := congrArg Fin.val h
    change (4 * d) * 2 + (finProdFinEquiv (a, finProdFinEquiv x)).val =
      (4 * d) * 2 + (finProdFinEquiv (b, finProdFinEquiv y)).val at h'
    omega
  have hpair := finProdFinEquiv.injective heq
  exact Prod.ext (congrArg (fun z : Fin 2 × Fin (r * n) => z.1) hpair)
    (finProdFinEquiv.injective (congrArg (fun z : Fin 2 × Fin (r * n) => z.2) hpair))

theorem prefixOrdinary_ne_diagonal {d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (x : Fin 2 × (Fin r × Fin n)) (y : Fin (4 * d) × Fin 2) :
    prefixOrdinaryPairIndex hfit x ≠ prefixDiagonalPairIndex hdiag y := by
  intro h
  have hv := congrArg Fin.val h
  have hy := (finProdFinEquiv y).isLt
  change (4 * d) * 2 + (finProdFinEquiv (x.1, finProdFinEquiv x.2)).val =
    (finProdFinEquiv y).val at hv
  omega

/-- FC2K uses all `Q = 6(n+8)` pairs at each stage: 48 for the 24
diagonal rectangles and 6n for the two ordinary networks. -/
theorem fc2k_prefix_pair_allocation (n : ℕ) :
    (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega

/-- Corner order follows the existing rectangle convention: low/high on the
first pair, high/low on the second. -/
def prefixCornerCode : Fin 4 → Fin 2 × Bool :=
  ![(0, false), (0, true), (1, true), (1, false)]

theorem prefixCornerCode_injective : Function.Injective prefixCornerCode := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [prefixCornerCode]

def prefixRectangleInput {P d Q : ℕ} (hfit : (4 * d) * 2 ≤ Q)
    (x : Fin (P * (4 * d)) × Fin 4) : (Fin P × Fin Q) × Bool :=
  let p : Fin P × Fin (4 * d) := finProdFinEquiv.symm x.1
  let c := prefixCornerCode x.2
  ((p.1, prefixDiagonalPairIndex hfit (p.2, c.1)), c.2)

theorem prefixRectangleInput_injective {P d Q : ℕ} (hfit : (4 * d) * 2 ≤ Q) :
    Function.Injective (prefixRectangleInput (P := P) hfit) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  let pi : Fin P × Fin (4 * d) := finProdFinEquiv.symm i
  let pj : Fin P × Fin (4 * d) := finProdFinEquiv.symm j
  change ((pi.1, prefixDiagonalPairIndex hfit (pi.2, (prefixCornerCode a).1)),
    (prefixCornerCode a).2) =
    ((pj.1, prefixDiagonalPairIndex hfit (pj.2, (prefixCornerCode b).1)),
      (prefixCornerCode b).2) at h
  have hstage := congrArg (fun z : (Fin P × Fin Q) × Bool => z.1.1) h
  have hpair := prefixDiagonalPairIndex_injective hfit
    (congrArg (fun z : (Fin P × Fin Q) × Bool => z.1.2) h)
  have hrect := congrArg (fun z : Fin (4 * d) × Fin 2 => z.1) hpair
  have hcode : prefixCornerCode a = prefixCornerCode b := Prod.ext
    (congrArg (fun z : Fin (4 * d) × Fin 2 => z.2) hpair)
    (congrArg (fun z : (Fin P × Fin Q) × Bool => z.2) h)
  have hi : i = j := finProdFinEquiv.symm.injective (Prod.ext hstage hrect)
  have ha : a = b := prefixCornerCode_injective hcode
  exact Prod.ext hi ha

def prefixOrdinaryInput {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q)
    (x : (Fin P × (Fin 2 × (Fin r × Fin n))) × Bool) : (Fin P × Fin Q) × Bool :=
  ((x.1.1, prefixOrdinaryPairIndex hfit x.1.2), x.2)

theorem prefixOrdinaryInput_injective {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) :
    Function.Injective (prefixOrdinaryInput (P := P) hfit) := by
  rintro ⟨⟨j, p⟩, s⟩ ⟨⟨j', p'⟩, s'⟩ h
  have hj := congrArg (fun z : (Fin P × Fin Q) × Bool => z.1.1) h
  have hp := prefixOrdinaryPairIndex_injective hfit
    (congrArg (fun z : (Fin P × Fin Q) × Bool => z.1.2) h)
  have hs := congrArg (fun z : (Fin P × Fin Q) × Bool => z.2) h
  exact Prod.ext (Prod.ext hj hp) hs

theorem prefixOrdinaryInput_ne_rectangle {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (x : (Fin P × (Fin 2 × (Fin r × Fin n))) × Bool)
    (y : Fin (P * (4 * d)) × Fin 4) :
    prefixOrdinaryInput hfit x ≠ prefixRectangleInput hdiag y := by
  intro h
  apply prefixOrdinary_ne_diagonal hfit hdiag x.1.2
    ((finProdFinEquiv.symm y.1).2, (prefixCornerCode y.2).1)
  exact congrArg (fun z : (Fin P × Fin Q) × Bool => z.1.2) h

/-- Place the actual retained FPF pair endpoints in the selected RP1
rectangles. The remaining endpoint values are not used by these rectangles. -/
theorem install_prefix_diagonal_rectangles {P d Q L n : ℕ}
    (hdiag : (4 * d) * 2 ≤ Q) (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (values : (Fin P × Fin Q) × Bool → pool n)
    (hinj : Function.Injective values)
    (hgap : ∀ j i, (values ((j, i), true)).val =
      (values ((j, i), false)).val + 2 ^ (j.val + 1))
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
          entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 0)) + 2 ^ (j.val + 1) ∧
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 2)) =
          entry b (packedRectangleCorner hs choice (Fin.castLE hrect t, 3)) + 2 ^ (j.val + 1)) := by
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

/-- Reindex stage, within-stage layer and edge into the ordinary pair
allocation. The network index is fixed to 0 for rows and 1 for columns. -/
def prefixNetworkInput {P d r n Q m : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hlen : m = P * r) (network : Fin 2)
    (x : Fin m × (Fin n × Bool)) : (Fin P × Fin Q) × Bool :=
  let p : Fin P × Fin r := finProdFinEquiv.symm (Fin.cast hlen x.1)
  prefixOrdinaryInput hfit ((p.1, (network, (p.2, x.2.1))), x.2.2)

theorem prefixNetworkInput_injective {P d r n Q m : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hlen : m = P * r) (network : Fin 2) :
    Function.Injective (prefixNetworkInput (n := n) hfit hlen network) := by
  rintro ⟨i, e, s⟩ ⟨j, f, t⟩ h
  have hp := prefixOrdinaryInput_injective hfit h
  have hs := congrArg (fun z : (Fin P × (Fin 2 × (Fin r × Fin n))) × Bool => z.2) hp
  have he := congrArg (fun z : (Fin P × (Fin 2 × (Fin r × Fin n))) × Bool => z.1.2.2.2) hp
  have hstage := congrArg (fun z : (Fin P × (Fin 2 × (Fin r × Fin n))) × Bool => z.1.1) hp
  have hlayer := congrArg (fun z : (Fin P × (Fin 2 × (Fin r × Fin n))) × Bool => z.1.2.2.1) hp
  have hi : i = j := by
    apply Fin.cast_injective hlen
    apply finProdFinEquiv.symm.injective
    exact Prod.ext hstage hlayer
  change e = f at he
  change s = t at hs
  exact Prod.ext hi (Prod.ext he hs)

theorem prefixNetworkInputs_separate {P d r n Q m m' : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hlen : m = P * r) (hlen' : m' = P * r)
    (x : Fin m × (Fin n × Bool)) (y : Fin m' × (Fin n × Bool)) :
    prefixNetworkInput hfit hlen (0 : Fin 2) x ≠ prefixNetworkInput hfit hlen' (1 : Fin 2) y := by
  intro h
  have hp := prefixOrdinaryInput_injective hfit h
  have hn := congrArg (fun z : (Fin P × (Fin 2 × (Fin r × Fin n))) × Bool => z.1.2.1) hp
  simp at hn

theorem prefixNetworkInput_ne_rectangle {P d r n Q m : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hlen : m = P * r) (network : Fin 2) (x : Fin m × (Fin n × Bool))
    (y : Fin (P * (4 * d)) × Fin 4) :
    prefixNetworkInput hfit hlen network x ≠ prefixRectangleInput hdiag y :=
  prefixOrdinaryInput_ne_rectangle hfit hdiag _ y

/-- Every physical ordinary pair has the exact power-of-two gap from its
stage, independently of the network or its placement. -/
theorem prefixNetwork_pair_gap {P d r n Q m : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hlen : m = P * r) (network : Fin 2)
    (values : (Fin P × Fin Q) × Bool → pool n)
    (hgap : ∀ j i, (values ((j, i), true)).val =
      (values ((j, i), false)).val + 2 ^ (j.val + 1))
    (i : Fin m) (edge : Fin n) :
    (values (prefixNetworkInput hfit hlen network (i, (edge, true)))).val =
      (values (prefixNetworkInput hfit hlen network (i, (edge, false)))).val +
        2 ^ ((finProdFinEquiv.symm (Fin.cast hlen i) : Fin P × Fin r).1.val + 1) :=
  hgap _ _

def prefixNetworkGap {P r m : ℕ} (hlen : m = P * r) (i : Fin m) (_edge : Fin n) : ℕ :=
  2 ^ ((finProdFinEquiv.symm (Fin.cast hlen i) : Fin P × Fin r).1.val + 1)

/-- Install both ordinary prefix networks after the diagonal endpoints have
been placed. Every supplied pair comes from the same injective population;
reserved diagonal values are avoided by the proved allocation split. -/
theorem install_prefix_ordinary_networks {P d r n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (values : (Fin P × Fin Q) × Bool → pool n) (hinj : Function.Injective values)
    (hgap : ∀ j i, (values ((j, i), true)).val =
      (values ((j, i), false)).val + 2 ^ (j.val + 1))
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
        entry b (e, (rows.get i).2 e) + prefixNetworkGap hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + prefixNetworkGap hclen (Fin.cast hcols i) e) ∧
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
      (prefixNetworkGap hrlen) (prefixNetworkGap hclen)
      (prefixNetwork_pair_gap hfit hrlen 0 values hgap)
      (prefixNetwork_pair_gap hfit hclen 1 values hgap)
  exact ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdisjoint,
    hrplaced, hcplaced, hrgap, hcgap, hfixed⟩

/-- Place the FPF diagonal pairs and both ordinary pair networks in one
square. The retained population and numerical packing gates are inputs; all
cell and value separation between these families is proved here. -/
theorem install_prefix_diagonal_and_ordinary {P d r n Q L B : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (values : (Fin P × Fin Q) × Bool → pool n) (hinj : Function.Injective values)
    (hgap : ∀ j i, (values ((j, i), true)).val =
      (values ((j, i), false)).val + 2 ^ (j.val + 1))
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
        entry b (e, (rows.get i).2 e) + prefixNetworkGap hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + prefixNetworkGap hclen (Fin.cast hcols i) e) ∧
      (∀ c ∈ base, entry b c = entry a c) := by
  obtain ⟨a', hplaced, hbasefixed, _⟩ :=
    install_prefix_diagonal_rectangles hdiag hrect hs choice values hinj hgap a base hfree
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
    install_prefix_ordinary_networks hfit hdiag values hinj hgap initial havoid rowPerms colPerms
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

end
end Sude
