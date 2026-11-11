import Sude.BridgeOrdinarySlots

/-! Reindex the actual selected bridge entries into the two PB networks. -/
namespace Sude
noncomputable section

/-- Reindex one network's layer/edge/side slot by stage and within-stage
layer. The two networks use opposite pairs of each selected block. -/
def bridgeNetworkInput {J r n m : ℕ} (hlen : m = J * r) (network : Bool)
    (x : Fin m × (Fin n × Bool)) : (Fin J × (Fin r × Fin n)) × (Bool × Bool) :=
  let p : Fin J × Fin r := finProdFinEquiv.symm (Fin.cast hlen x.1)
  ((p.1, (p.2, x.2.1)), (network, x.2.2))

theorem bridgeNetworkInput_injective {J r n m : ℕ} (hlen : m = J * r) (network : Bool) :
    Function.Injective (bridgeNetworkInput (n := n) hlen network) := by
  rintro ⟨u, ⟨e, side⟩⟩ ⟨v, ⟨f, side'⟩⟩ heq
  let p : Fin J × Fin r := finProdFinEquiv.symm (Fin.cast hlen u)
  let q : Fin J × Fin r := finProdFinEquiv.symm (Fin.cast hlen v)
  change ((p.1, (p.2, e)), (network, side)) = ((q.1, (q.2, f)), (network, side')) at heq
  have hj := congrArg (fun z : (Fin J × (Fin r × Fin n)) × (Bool × Bool) => z.1.1) heq
  have hl := congrArg (fun z : (Fin J × (Fin r × Fin n)) × (Bool × Bool) => z.1.2.1) heq
  have hed : e = f := congrArg (fun z : (Fin J × (Fin r × Fin n)) × (Bool × Bool) => z.1.2.2) heq
  have hs : side = side' := congrArg (fun z : (Fin J × (Fin r × Fin n)) × (Bool × Bool) => z.2.2) heq
  have huv : u = v := by
    apply Fin.cast_injective hlen
    apply finProdFinEquiv.symm.injective
    exact Prod.ext hj hl
  subst v
  subst f
  subst side'
  rfl

theorem bridgeNetworkInput_separate {J r n m m' : ℕ} (hlen : m = J * r)
    (hlen' : m' = J * r) (x : Fin m × (Fin n × Bool)) (y : Fin m' × (Fin n × Bool)) :
    bridgeNetworkInput hlen false x ≠ bridgeNetworkInput hlen' true y := by
  intro h
  have hn := congrArg (fun z : (Fin J × (Fin r × Fin n)) × (Bool × Bool) => z.2.1) h
  simp [bridgeNetworkInput] at hn

/-- The gap assigned to one ordinary network edge is the actual selected
double block's gap, for both networks. -/
def bridgeNetworkGap {J r n d k m : ℕ} (hlen : m = J * r)
    (hfit : 4 * d + r * n ≤ k) (batches : ℕ → List DoublePair)
    (layer : Fin m) (edge : Fin n) : ℕ :=
  let p : Fin J × Fin r := finProdFinEquiv.symm (Fin.cast hlen layer)
  selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit (p.2, edge)) p.1

/-- The actual prescribed-pool value assigned to a network slot. -/
def bridgeNetworkValue {J r n d k m : ℕ} (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hpositive : ∀ j < J, 0 < radii j) (hlen : m = J * r) (network : Bool)
    (x : Fin m × (Fin n × Bool)) : pool n :=
  ⟨bridgeOrdinaryEndpoint initial radii batches hvalid hfit (bridgeNetworkInput hlen network x),
    (bridgeOrdinaryEndpoint_pool_avoids bmor upper initial radii batches hvalid hfit hn hnmax
      hpositive (bridgeNetworkInput hlen network x)).1⟩

theorem bridgeNetworkValue_injective {J r n d k m : ℕ} (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hpositive : ∀ j < J, 0 < radii j) (hlen : m = J * r) (network : Bool) :
    Function.Injective (bridgeNetworkValue bmor upper initial radii batches hvalid hfit
      hn hnmax hpositive hlen network) := by
  intro x y heq
  apply bridgeNetworkInput_injective hlen network
  apply bridgeOrdinaryEndpoint_injective initial radii batches hvalid hfit hpositive
  exact congrArg Subtype.val heq

theorem bridgeNetworkValues_separate {J r n d k m m' : ℕ} (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hpositive : ∀ j < J, 0 < radii j) (hlen : m = J * r) (hlen' : m' = J * r)
    (x : Fin m × (Fin n × Bool)) (y : Fin m' × (Fin n × Bool)) :
    (bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive hlen false x).val ≠
      (bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive hlen' true y).val := by
  intro heq
  apply bridgeNetworkInput_separate hlen hlen' x y
  apply bridgeOrdinaryEndpoint_injective initial radii batches hvalid hfit hpositive
  exact heq

theorem bridgeNetworkValue_gap {J r n d k m : ℕ} (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hpositive : ∀ j < J, 0 < radii j) (hlen : m = J * r) (network : Bool)
    (layer : Fin m) (edge : Fin n) :
    let gap := bridgeNetworkGap hlen hfit batches layer edge
    0 < gap ∧ 2 ∣ gap ∧
      (bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive hlen
        network (layer, (edge, true))).val =
      (bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive hlen
        network (layer, (edge, false))).val + gap := by
  let p : Fin J × Fin r := finProdFinEquiv.symm (Fin.cast hlen layer)
  exact bridgeOrdinary_pair_gap initial radii batches hvalid hfit p.1 (p.2, edge) network

theorem bridgeNetworkValue_not_initial {J r n d k m : ℕ} (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hpositive : ∀ j < J, 0 < radii j) (hlen : m = J * r) (network : Bool)
    (x : Fin m × (Fin n × Bool)) :
    (bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive hlen network x).val ∉ initial :=
  (bridgeOrdinaryEndpoint_pool_avoids bmor upper initial radii batches hvalid hfit hn hnmax
    hpositive (bridgeNetworkInput hlen network x)).2

theorem bridgeNetworkValue_ne_diagonal {J r n d k m : ℕ} (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hdiag : 4 * d ≤ k)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (hlen : m = J * r) (network : Bool) (x : Fin m × (Fin n × Bool))
    (t : Fin (J * (4 * d))) (side : Fin 4) :
    (bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive hlen network x).val ≠
      bridgeStageEndpoint n initial radii batches k J hvalid (bridgeDiagonalBlockSelect hdiag t, side) :=
  bridgeOrdinaryEndpoint_ne_diagonal initial radii batches hvalid hfit hdiag hpositive
    (bridgeNetworkInput hlen network x) t side

/-- Install all ordinary bridge pairs into the two PB permutation-layer
networks, using actual selected pool values. Prior cells may contain initial
reserved values or the allocated diagonal-rectangle endpoints. -/
theorem pack_and_install_bridge_ordinary_networks {J r n d k L : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (initial : Finset ℕ)
    (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hdiag : 4 * d ≤ k)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrcount : rowPerms.length = J * r) (hccount : colPerms.length = J * r)
    (reservedCells : Finset (Cell n))
    (hrowDerange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcolDerange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (hrowLoad : ∀ i, (LayerPacking.rowUsed reservedCells i).card ≤ L)
    (hcolLoad : ∀ i, (LayerPacking.colUsed reservedCells i).card ≤ L)
    (hcapacity : 4 * (L + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial ∨
      ∃ t : Fin (J * (4 * d)), ∃ side : Fin 4,
        entry a c = bridgeStageEndpoint n initial radii batches k J hvalid
          (bridgeDiagonalBlockSelect hdiag t, side)) :
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrlen : rows.length = rowPerms.length)
      (hclen : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers reservedCells rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (reservedCells ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ z ∈ LayerPacking.layersSupport rows, z ∉ reservedCells ∧
        z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols), z ∉ reservedCells ∧
        z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive
          hrcount false (Fin.cast hrlen x.1, x.2)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive
          hccount true (Fin.cast hclen x.1, x.2)).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + bridgeNetworkGap hrcount hfit batches (Fin.cast hrlen i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + bridgeNetworkGap hccount hfit batches (Fin.cast hclen i) e) ∧
      (∀ c ∈ reservedCells, entry b c = entry a c) ∧
      (∀ r₀, (((LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)).filter
        (fun z => z.1 = r₀)).card = 2 * (rowPerms.length + colPerms.length)) ∧
      (∀ c₀, (((LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)).filter
        (fun z => z.2 = c₀)).card = 2 * (rowPerms.length + colPerms.length)) := by
  let rv := bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive hrcount false
  let cv := bridgeNetworkValue bmor upper initial radii batches hvalid hfit hn hnmax hpositive hccount true
  let rg := bridgeNetworkGap hrcount hfit batches
  let cg := bridgeNetworkGap hccount hfit batches
  have hrinj : Function.Injective rv :=
    bridgeNetworkValue_injective bmor upper initial radii batches hvalid hfit hn hnmax hpositive hrcount false
  have hcinj : Function.Injective cv :=
    bridgeNetworkValue_injective bmor upper initial radii batches hvalid hfit hn hnmax hpositive hccount true
  have hsep : ∀ x y, (rv x).val ≠ (cv y).val := by
    intro x y
    exact bridgeNetworkValues_separate bmor upper initial radii batches hvalid hfit hn hnmax hpositive
      hrcount hccount x y
  have hravoid : ∀ x c, c ∈ reservedCells → (rv x).val ≠ entry a c := by
    intro x c hc heq
    rcases hreserved c hc with hinit | ⟨t, side, hdiagval⟩
    · apply bridgeNetworkValue_not_initial bmor upper initial radii batches hvalid hfit hn hnmax
        hpositive hrcount false x
      change (rv x).val ∈ initial
      rw [heq]
      exact hinit
    · exact (bridgeNetworkValue_ne_diagonal bmor upper initial radii batches hvalid hfit hdiag hn hnmax
        hpositive hrcount false x t side) (heq.trans hdiagval)
  have hcavoid : ∀ x c, c ∈ reservedCells → (cv x).val ≠ entry a c := by
    intro x c hc heq
    rcases hreserved c hc with hinit | ⟨t, side, hdiagval⟩
    · apply bridgeNetworkValue_not_initial bmor upper initial radii batches hvalid hfit hn hnmax
        hpositive hccount true x
      change (cv x).val ∈ initial
      rw [heq]
      exact hinit
    · exact (bridgeNetworkValue_ne_diagonal bmor upper initial radii batches hvalid hfit hdiag hn hnmax
        hpositive hccount true x t side) (heq.trans hdiagval)
  have hrgap : ∀ i e, (rv (i, (e, true))).val = (rv (i, (e, false))).val + rg i e := by
    intro i e
    exact (bridgeNetworkValue_gap bmor upper initial radii batches hvalid hfit hn hnmax hpositive
      hrcount false i e).2.2
  have hcgap : ∀ i e, (cv (i, (e, true))).val = (cv (i, (e, false))).val + cg i e := by
    intro i e
    exact (bridgeNetworkValue_gap bmor upper initial radii batches hvalid hfit hn hnmax hpositive
      hccount true i e).2.2
  obtain ⟨rows, cols, hrlen, hclen, b, hrmap, hcmap, hrpacked, hcpacked, hdisjoint,
      hrowsafe, hcolsafe, hrvalues, hcvalues, hrphysical, hcphysical, hfixed,
      _, _, hrowbalance, hcolbalance⟩ :=
    LayerPacking.pack_and_install_two_networks rowPerms colPerms reservedCells hrowDerange hcolDerange
      hrowLoad hcolLoad hcapacity a rv cv hrinj hcinj hsep hravoid hcavoid rg cg hrgap hcgap
  exact ⟨rows, cols, hrlen, hclen, b, hrmap, hcmap, hrpacked, hcpacked, hdisjoint,
    hrowsafe, hcolsafe, hrvalues, hcvalues, hrphysical, hcphysical, hfixed, hrowbalance, hcolbalance⟩

end
end Sude
