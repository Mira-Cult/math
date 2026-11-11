import Sude.BridgeOrdinaryNetworks
import Sude.PackedRectangleLoads

/-! Connect installed diagonal bridge rectangles to ordinary PB networks. -/
namespace Sude
noncomputable section

/-- The allocated bridge subset's actual rectangle cells. -/
def allocatedBridgeRectangleSupport {J d L n : ℕ} (hrect : J * (4 * d) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) : Finset (Cell n) :=
  (Finset.univ : Finset (Fin (J * (4 * d)) × Fin 4)).image
    (fun x => packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2))

/-- Physical cells belonging to a specified set of joint RP1 labels. -/
def packedRectangleSupportOn {L n : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (labels : Finset (Fin L)) : Finset (Cell n) :=
  labels.biUnion fun i => rectangleCells (RectanglePacking.firstRow hs i)
    (RectanglePacking.secondRow hs i) (RectanglePacking.firstColumn hs choice i)
    (RectanglePacking.secondColumn hs choice i)

/-- The bridge rectangles are automatically free of the center and of any
previously reserved rectangles with different joint RP1 labels. -/
theorem allocatedBridge_free_of_other_rectangles {J d L n : ℕ}
    (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (other : Finset (Fin L)) (hn : 0 < n)
    (hother : ∀ t : Fin (J * (4 * d)), bridgeDiagonalRectangle hrect t ∉ other) :
    ∀ t : Fin (J * (4 * d)), Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)))
      (packedRectangleSupportOn hs choice other ∪ {(centerIndex n hn, centerIndex n hn)}) := by
  intro t
  apply Finset.disjoint_left.mpr
  intro c hc hreserved
  rcases Finset.mem_union.mp hreserved with hotherCell | hcenter
  · obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.mp hotherCell
    have hne : bridgeDiagonalRectangle hrect t ≠ i := by
      intro heq
      apply hother t
      rw [heq]
      exact hi
    exact Finset.disjoint_left.mp
      (RectanglePacking.rectangle_cells_disjoint hs choice (bridgeDiagonalRectangle hrect t) i hne) hc hci
  · have heq : c = (centerIndex n hn, centerIndex n hn) := Finset.mem_singleton.mp hcenter
    subst c
    exact RectanglePacking.rectangle_avoids_center hs hn choice (bridgeDiagonalRectangle hrect t) hc

theorem allocatedBridgeRectangleSupport_subset {J d L n : ℕ} (hrect : J * (4 * d) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) :
    allocatedBridgeRectangleSupport hrect hs choice ⊆ packedRectangleSupport hs choice := by
  intro c hc
  obtain ⟨⟨t, side⟩, _, rfl⟩ := Finset.mem_image.mp hc
  exact Finset.mem_image.mpr ⟨(bridgeDiagonalRectangle hrect t, side), Finset.mem_univ _, rfl⟩

theorem allocatedBridgeRectangle_cells_subset {J d L n : ℕ} (hrect : J * (4 * d) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (t : Fin (J * (4 * d))) :
    rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
      (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
      (RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t))
      (RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) ⊆
        allocatedBridgeRectangleSupport hrect hs choice := by
  intro c hc
  rcases (mem_rectangleCells _ _ _ _ _).mp hc with h | h | h | h
  · rw [h]
    exact Finset.mem_image.mpr ⟨(t, 0), Finset.mem_univ _, rfl⟩
  · rw [h]
    exact Finset.mem_image.mpr ⟨(t, 1), Finset.mem_univ _, rfl⟩
  · rw [h]
    exact Finset.mem_image.mpr ⟨(t, 2), Finset.mem_univ _, rfl⟩
  · rw [h]
    exact Finset.mem_image.mpr ⟨(t, 3), Finset.mem_univ _, rfl⟩

/-- Diagonal trades cannot alter an ordinary-network cell outside the
allocated rectangle support, even when many trades are composed. -/
theorem allocatedBridgeTrades_preserve_outside {J d L n : ℕ} (hrect : J * (4 * d) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (labels : List (Fin (J * (4 * d)))) (c : Cell n)
    (hc : c ∉ allocatedBridgeRectangleSupport hrect hs choice) :
    entry (packedTradeSequence hs choice a (labels.map (bridgeDiagonalRectangle hrect))) c = entry a c := by
  apply packedTradeSequence_fixes_outside
  intro i hi hm
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hi
  exact hc (allocatedBridgeRectangle_cells_subset hrect hs choice t hm)

/-- Retained diagonal endpoint values still furnish the equal-gap equations
needed by the physical rectangle trade. -/
theorem allocatedBridgeRectangle_gap {J d L n k : ℕ} (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hdiag : 4 * d ≤ k) (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (hplace : ∀ t side,
      entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        bridgeStageEndpoint n initial radii batches k J hvalid (bridgeDiagonalBlockSelect hdiag t, side))
    (t : Fin (J * (4 * d))) :
    let g := selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
      (bridgeDiagonalBlockSelect hdiag t).1
    0 < g ∧
      entry a (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) =
        entry a (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t)) + g ∧
      entry a (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t)) =
        entry a (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) + g := by
  let j := (bridgeDiagonalBlockSelect hdiag t).1
  let i := (bridgeDiagonalBlockSelect hdiag t).2
  have hv := bridgeStageBlock_valid n initial radii batches k J hvalid j i
  rcases hv with ⟨_, _, _, _, _, _, hfirst, hsecond, heq⟩
  have hgap := bridgeStageBlock_gap n initial radii batches k J hvalid j i
  refine ⟨by rw [hgap]; omega, ?_, ?_⟩
  · have ha := hplace t 1
    have hb := hplace t 0
    change entry a (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
        RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) = _ at ha
    change entry a (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
        RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t)) = _ at hb
    rw [ha, hb, hgap]
    change (bridgeStageBlock n initial radii batches k J hvalid j i).high₁ =
      (bridgeStageBlock n initial radii batches k J hvalid j i).low₁ +
        ((bridgeStageBlock n initial radii batches k J hvalid j i).high₁ -
          (bridgeStageBlock n initial radii batches k J hvalid j i).low₁)
    omega
  · have ha := hplace t 2
    have hb := hplace t 3
    change entry a (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
        RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t)) = _ at ha
    change entry a (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
        RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) = _ at hb
    rw [ha, hb, hgap]
    change (bridgeStageBlock n initial radii batches k J hvalid j i).high₂ =
      (bridgeStageBlock n initial radii batches k J hvalid j i).low₂ +
        ((bridgeStageBlock n initial radii batches k J hvalid j i).high₁ -
          (bridgeStageBlock n initial radii batches k J hvalid j i).low₁)
    omega

/-- The reserved-cell value condition required by the ordinary-network
theorem follows from actual diagonal placement and prior-cell preservation. -/
theorem allocatedBridgeReservation_values {J d L n k : ℕ}
    (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hdiag : 4 * d ≤ k) (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a a' : Cell n ≃ Fin (n * n)) (base : Finset (Cell n))
    (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hfixed : ∀ c ∈ base, entry a' c = entry a c)
    (hplace : ∀ t side,
      entry a' (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        bridgeStageEndpoint n initial radii batches k J hvalid (bridgeDiagonalBlockSelect hdiag t, side)) :
    ∀ c ∈ base ∪ allocatedBridgeRectangleSupport hrect hs choice,
      entry a' c ∈ initial ∨ ∃ t : Fin (J * (4 * d)), ∃ side : Fin 4,
        entry a' c = bridgeStageEndpoint n initial radii batches k J hvalid
          (bridgeDiagonalBlockSelect hdiag t, side) := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · left
    rw [hfixed c hc]
    exact hbase c hc
  · obtain ⟨⟨t, side⟩, _, rfl⟩ := Finset.mem_image.mp hc
    exact Or.inr ⟨t, side, hplace t side⟩

/-- The precise PB8 two-cell allowance for the allocated bridge rectangles,
in addition to any separately bounded prior line load. -/
theorem allocatedBridgeReservation_load {J d L n B : ℕ}
    (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (base : Finset (Cell n))
    (hrow : ∀ r, (LayerPacking.rowUsed base r).card ≤ B)
    (hcol : ∀ c, (LayerPacking.colUsed base c).card ≤ B) :
    (∀ r, (LayerPacking.rowUsed (base ∪ allocatedBridgeRectangleSupport hrect hs choice) r).card ≤ B + 2) ∧
    (∀ c, (LayerPacking.colUsed (base ∪ allocatedBridgeRectangleSupport hrect hs choice) c).card ≤ B + 2) :=
  packedRectangleSupport_union_load hs choice base _ (allocatedBridgeRectangleSupport_subset hrect hs choice)
    hrow hcol

/-- Earlier rectangles and new bridge rectangles share the same two-cell
RP1 allowance; they are not charged twice. -/
theorem allocatedBridge_joint_reservation_load {J d L n B : ℕ}
    (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (base ordinary : Finset (Cell n))
    (hbase : base ⊆ ordinary ∪ packedRectangleSupport hs choice)
    (hrow : ∀ r, (LayerPacking.rowUsed ordinary r).card ≤ B)
    (hcol : ∀ c, (LayerPacking.colUsed ordinary c).card ≤ B) :
    (∀ r, (LayerPacking.rowUsed (base ∪ allocatedBridgeRectangleSupport hrect hs choice) r).card ≤ B + 2) ∧
    (∀ c, (LayerPacking.colUsed (base ∪ allocatedBridgeRectangleSupport hrect hs choice) c).card ≤ B + 2) :=
  packedRectangle_joint_reservation_load hs choice base ordinary _ hbase
    (allocatedBridgeRectangleSupport_subset hrect hs choice) hrow hcol

/-- With d=6 and three row and three column layers per bridge stage,
PB9's full-stage load also pays for any J bridge stages and the prior
ordinary layers, without double-counting the joint rectangles. -/
theorem fc2k_bridge_pb9_matching_capacity (n S J : ℕ) (hJS : J ≤ S)
    (hpb9 : 4 * (2 * 6 * S + 2) + 8 < n) :
    4 * ((2 * 6 * (S - J) + 2) + 2 * (J * 3) + 2 * (J * 3)) + 8 < n := by
  omega

/-- First install the actual diagonal bridge blocks in RP1 rectangles,
then place every remaining ordinary bridge pair in two balanced physical
networks. The ordinary matching reserves and preserves all diagonal cells. -/
theorem install_bridge_diagonal_and_ordinary_networks {J r n d k L B : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (initial : Finset ℕ)
    (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hdiag : 4 * d ≤ k)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrcount : rowPerms.length = J * r) (hccount : colPerms.length = J * r)
    (hrowDerange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcolDerange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (a : Cell n ≃ Fin (n * n)) (base ordinary : Finset (Cell n))
    (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hbaseGeometry : base ⊆ ordinary ∪ packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice))
    (hrowLoad : ∀ r₀, (LayerPacking.rowUsed ordinary r₀).card ≤ B)
    (hcolLoad : ∀ c₀, (LayerPacking.colUsed ordinary c₀).card ≤ B)
    (hfree : ∀ t : Fin (J * (4 * d)), Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))) base)
    (hcapacity : 4 * ((B + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n) :
    let choice := bridgeDiagonalChoice hrect otherChoice
    let reserved := base ∪ allocatedBridgeRectangleSupport hrect hs choice
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrlen : rows.length = rowPerms.length)
      (hclen : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers reserved rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (reserved ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ z ∈ LayerPacking.layersSupport rows, z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
        z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
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
      (∀ c ∈ base, entry b c = entry a c) ∧
      (∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        bridgeStageEndpoint n initial radii batches k J hvalid (bridgeDiagonalBlockSelect hdiag t, side)) ∧
      (∀ r₀, (((LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)).filter
        (fun z => z.1 = r₀)).card = 2 * (rowPerms.length + colPerms.length)) ∧
      (∀ c₀, (((LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)).filter
        (fun z => z.2 = c₀)).card = 2 * (rowPerms.length + colPerms.length)) := by
  let choice := bridgeDiagonalChoice hrect otherChoice
  let added := allocatedBridgeRectangleSupport hrect hs choice
  let reserved := base ∪ added
  obtain ⟨a', hplace, hfixed, _⟩ := install_allocated_bridge_diagonal_blocks bmor upper n initial radii
    batches k J d L hvalid hn hnmax hpositive hdiag hrect hs otherChoice a base hbase hfree
  have hloads := allocatedBridge_joint_reservation_load hrect hs choice base ordinary
    hbaseGeometry hrowLoad hcolLoad
  have hvalues := allocatedBridgeReservation_values initial radii batches hvalid hdiag hrect hs choice
    a a' base hbase hfixed hplace
  obtain ⟨rows, cols, hrlen, hclen, b, hrmap, hcmap, hrpacked, hcpacked, hdisjoint,
      hrowsafe, hcolsafe, hrvalues, hcvalues, hrphysical, hcphysical, hnewfixed, hrowbalance, hcolbalance⟩ :=
    pack_and_install_bridge_ordinary_networks bmor upper initial radii batches hvalid hfit hdiag
      hn hnmax hpositive rowPerms colPerms hrcount hccount reserved hrowDerange hcolDerange
      hloads.1 hloads.2 hcapacity a' hvalues
  refine ⟨rows, cols, hrlen, hclen, b, hrmap, hcmap, hrpacked, hcpacked, hdisjoint,
    hrowsafe, hcolsafe, hrvalues, hcvalues, hrphysical, hcphysical, ?_, ?_, hrowbalance, hcolbalance⟩
  · intro c hc
    exact (hnewfixed c (Finset.mem_union_left _ hc)).trans (hfixed c hc)
  · intro t side
    have hc : packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side) ∈ reserved := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(t, side), Finset.mem_univ _, rfl⟩
    exact (hnewfixed _ hc).trans (hplace t side)

/-- Once the ordinary networks are placed outside the reserved rectangles,
any duplicate-free set of diagonal switches leaves every ordinary entry
untouched while producing the exact full-line effects. -/
theorem allocatedBridgeTrades_preserve_networks {J d L n k : ℕ}
    (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hdiag : 4 * d ≤ k) (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (hL : 3 ≤ L) (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (base : Finset (Cell n)) (rows cols : List (LayerPacking.Layer n))
    (hfree : ∀ t : Fin (J * (4 * d)), Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t))) base)
    (hplace : ∀ t side,
      entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        bridgeStageEndpoint n initial radii batches k J hvalid (bridgeDiagonalBlockSelect hdiag t, side))
    (hrowsafe : ∀ z ∈ LayerPacking.layersSupport rows,
      z ∉ allocatedBridgeRectangleSupport hrect hs choice)
    (hcolsafe : ∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
      z ∉ allocatedBridgeRectangleSupport hrect hs choice)
    (labels : List (Fin (J * (4 * d)))) (hnodup : labels.Nodup) (hn : 0 < n) :
    let result := packedTradeSequence hs choice a (labels.map (bridgeDiagonalRectangle hrect))
    (∀ r₀, rowSum result r₀ = rowSum a r₀) ∧
    (∀ c₀, columnSum result c₀ = columnSum a c₀) ∧
    (mainSum result : ℤ) = (mainSum a : ℤ) +
      (labels.map fun t => if choice (bridgeDiagonalRectangle hrect t) then
        (selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
          (bridgeDiagonalBlockSelect hdiag t).1 : ℤ) else 0).sum ∧
    (antiSum result : ℤ) = (antiSum a : ℤ) +
      (labels.map fun t => if choice (bridgeDiagonalRectangle hrect t) then 0 else
        (selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
          (bridgeDiagonalBlockSelect hdiag t).1 : ℤ)).sum ∧
    Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
    entry result (centerIndex n hn, centerIndex n hn) = entry a (centerIndex n hn, centerIndex n hn) ∧
    (∀ c ∈ base, entry result c = entry a c) ∧
    (∀ z ∈ LayerPacking.layersSupport rows, entry result z = entry a z) ∧
    (∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols), entry result z = entry a z) := by
  have hgaps : ∀ t,
      entry a (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) =
        entry a (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t)) +
            selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
              (bridgeDiagonalBlockSelect hdiag t).1 ∧
      entry a (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t)) =
        entry a (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) +
            selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
              (bridgeDiagonalBlockSelect hdiag t).1 :=
    fun t => (allocatedBridgeRectangle_gap initial radii batches hvalid hdiag hrect hs choice a hplace t).2
  have ht := selected_bridge_trade_sequence batches hs hL choice (bridgeDiagonalBlockSelect hdiag)
    (bridgeDiagonalRectangle hrect) (bridgeDiagonalRectangle_injective hrect)
    a base hfree hgaps labels hnodup hn
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1,
    ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1, ?_, ?_⟩
  · intro z hz
    exact allocatedBridgeTrades_preserve_outside hrect hs choice a labels z (hrowsafe z hz)
  · intro z hz
    exact allocatedBridgeTrades_preserve_outside hrect hs choice a labels z (hcolsafe z hz)

/-- Two actual diagonal orientations can be compared with signed effects
while every installed ordinary-network entry remains exactly unchanged. -/
theorem allocatedBridgeOrientations_preserve_networks {J d L n k : ℕ}
    (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hdiag : 4 * d ≤ k) (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (hL : 3 ≤ L) (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (base : Finset (Cell n)) (rows cols : List (LayerPacking.Layer n))
    (hfree : ∀ t : Fin (J * (4 * d)), Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t))) base)
    (hplace : ∀ t side,
      entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        bridgeStageEndpoint n initial radii batches k J hvalid (bridgeDiagonalBlockSelect hdiag t, side))
    (hrowsafe : ∀ z ∈ LayerPacking.layersSupport rows,
      z ∉ allocatedBridgeRectangleSupport hrect hs choice)
    (hcolsafe : ∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
      z ∉ allocatedBridgeRectangleSupport hrect hs choice)
    (before after : List (Fin (J * (4 * d)))) (hbefore : before.Nodup) (hafter : after.Nodup)
    (hn : 0 < n) :
    let baseline := packedTradeSequence hs choice a (before.map (bridgeDiagonalRectangle hrect))
    let result := packedTradeSequence hs choice a (after.map (bridgeDiagonalRectangle hrect))
    (∀ r₀, rowSum result r₀ = rowSum baseline r₀) ∧
    (∀ c₀, columnSum result c₀ = columnSum baseline c₀) ∧
    (mainSum result : ℤ) - (mainSum baseline : ℤ) =
      (after.map fun t => if choice (bridgeDiagonalRectangle hrect t) then
        (selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
          (bridgeDiagonalBlockSelect hdiag t).1 : ℤ) else 0).sum -
      (before.map fun t => if choice (bridgeDiagonalRectangle hrect t) then
        (selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
          (bridgeDiagonalBlockSelect hdiag t).1 : ℤ) else 0).sum ∧
    (antiSum result : ℤ) - (antiSum baseline : ℤ) =
      (after.map fun t => if choice (bridgeDiagonalRectangle hrect t) then 0 else
        (selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
          (bridgeDiagonalBlockSelect hdiag t).1 : ℤ)).sum -
      (before.map fun t => if choice (bridgeDiagonalRectangle hrect t) then 0 else
        (selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
          (bridgeDiagonalBlockSelect hdiag t).1 : ℤ)).sum ∧
    Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
    entry result (centerIndex n hn, centerIndex n hn) =
      entry baseline (centerIndex n hn, centerIndex n hn) ∧
    (∀ c ∈ base, entry result c = entry baseline c) ∧
    (∀ z ∈ LayerPacking.layersSupport rows, entry result z = entry baseline z) ∧
    (∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
      entry result z = entry baseline z) := by
  have hgaps : ∀ t,
      entry a (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) =
        entry a (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t)) +
            selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
              (bridgeDiagonalBlockSelect hdiag t).1 ∧
      entry a (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect t)) =
        entry a (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
          RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect t)) +
            selectedBridgeGap batches (bridgeDiagonalBlockSelect hdiag t).2
              (bridgeDiagonalBlockSelect hdiag t).1 :=
    fun t => (allocatedBridgeRectangle_gap initial radii batches hvalid hdiag hrect hs choice a hplace t).2
  have hdifference := selected_bridge_orientation_difference batches hs hL choice
    (bridgeDiagonalBlockSelect hdiag) (bridgeDiagonalRectangle hrect)
    (bridgeDiagonalRectangle_injective hrect) a base hfree hgaps before after hbefore hafter hn
  refine ⟨hdifference.1, hdifference.2.1, hdifference.2.2.1, hdifference.2.2.2.1,
    hdifference.2.2.2.2.1, hdifference.2.2.2.2.2.1, hdifference.2.2.2.2.2.2.1,
    hdifference.2.2.2.2.2.2.2, ?_, ?_⟩
  · intro z hz
    exact (allocatedBridgeTrades_preserve_outside hrect hs choice a after z (hrowsafe z hz)).trans
      (allocatedBridgeTrades_preserve_outside hrect hs choice a before z (hrowsafe z hz)).symm
  · intro z hz
    exact (allocatedBridgeTrades_preserve_outside hrect hs choice a after z (hcolsafe z hz)).trans
      (allocatedBridgeTrades_preserve_outside hrect hs choice a before z (hcolsafe z hz)).symm

end
end Sude
