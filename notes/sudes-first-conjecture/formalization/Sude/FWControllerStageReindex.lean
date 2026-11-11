import Sude.FWPhysicalDoubleBlockCells
import Sude.PrefixPhysicalSlotGeometry

/-! Stage-preserving reindexing of actual bridge and wide pair cells from
network-major prefix labels to block-major FW controller labels. This is
physical slot geometry and invoice transport, not an invoice bound. -/

namespace Sude
noncomputable section

/-- The controller's block-major label for each diagonal or ordinary pair. -/
def fwControllerStagePairBlock (n : ℕ) : PrefixStagePair 6 3 n → Fin (3 * (n + 8)) × Fin 2
  | Sum.inl (rect, pair) => (Fin.castLE (by omega) rect, pair)
  | Sum.inr (network, edge) => (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, network)

theorem fwControllerStagePairBlock_injective (n : ℕ) :
    Function.Injective (fwControllerStagePairBlock n) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      dsimp [fwControllerStagePairBlock] at h
      have hrect := Fin.castLE_injective (show 4 * 6 ≤ 3 * (n + 8) by omega) (congrArg Prod.fst h)
      have hp := congrArg Prod.snd h
      exact congrArg Sum.inl (Prod.ext hrect hp)
    | inr y =>
      dsimp [fwControllerStagePairBlock] at h
      have hb := congrArg (fun z : Fin (3 * (n + 8)) × Fin 2 => z.1.val) h
      have hr := x.1.isLt
      change x.1.val = 4 * 6 + (finProdFinEquiv y.2).val at hb
      omega
  | inr x =>
    cases y with
    | inl y =>
      dsimp [fwControllerStagePairBlock] at h
      have hb := congrArg (fun z : Fin (3 * (n + 8)) × Fin 2 => z.1.val) h
      have hr := y.1.isLt
      change 4 * 6 + (finProdFinEquiv x.2).val = y.1.val at hb
      omega
    | inr y =>
      dsimp [fwControllerStagePairBlock] at h
      have he := bridgeOrdinaryBlockIndex_injective (by omega : 4 * 6 + 3 * n ≤ 3 * (n + 8))
        (congrArg Prod.fst h)
      have hp := congrArg Prod.snd h
      exact congrArg Sum.inr (Prod.ext hp he)

/-- Controller block/pair labels cover exactly the diagonal and ordinary pairs. -/
theorem fwControllerStagePairBlock_bijective (n : ℕ) :
    Function.Bijective (fwControllerStagePairBlock n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fwControllerStagePairBlock_injective n, ?_⟩
  simp only [PrefixStagePair, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- Reindex network-major prefix pair slots into block-major controller slots. -/
def fwPrefixToControllerPair (n : ℕ) : Equiv.Perm (Fin (6 * (n + 8))) :=
  (Equiv.ofBijective (prefixStagePairSlot (d := 6) (layers := 3) (n := n)
    (Q := 6 * (n + 8)) (by omega) (by omega))
    (prefixStagePairSlot_bijective (by omega) (by omega) (by omega))).symm.trans
  ((Equiv.ofBijective (fwControllerStagePairBlock n) (fwControllerStagePairBlock_bijective n)).trans
    (finProdFinEquiv.trans (finCongr (by omega))))

theorem fwPrefixToControllerPair_diagonal (n : ℕ) (rect : Fin (4 * 6)) (pair : Fin 2) :
    fwPrefixToControllerPair n (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)) =
      Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
        (finProdFinEquiv (Fin.castLE (by omega : 4 * 6 ≤ 3 * (n + 8)) rect, pair)) := by
  unfold fwPrefixToControllerPair
  simp only [Equiv.trans_apply, Equiv.ofBijective_apply, finCongr_apply]
  rw [show prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair) =
    prefixStagePairSlot (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (Sum.inl (rect,pair)) by rfl]
  simp [fwControllerStagePairBlock]

theorem fwPrefixToControllerPair_ordinary (n : ℕ) (network : Fin 2) (edge : Fin 3 × Fin n) :
    fwPrefixToControllerPair n (prefixOrdinaryPairIndex
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,edge)) =
      Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
        (finProdFinEquiv (bridgeOrdinaryBlockIndex (show 4 * 6 + 3 * n ≤ 3 * (n + 8) by omega) edge, network)) := by
  unfold fwPrefixToControllerPair
  simp only [Equiv.trans_apply, Equiv.ofBijective_apply, finCongr_apply]
  rw [show prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,edge) =
    prefixStagePairSlot (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (Sum.inr (network,edge)) by rfl]
  simp [fwControllerStagePairBlock]


/-- The diagonal slots are unchanged by the reindexing. -/
theorem fwPrefixToControllerPair_diagonal_fixed (n : ℕ) (rect : Fin (4 * 6)) (pair : Fin 2) :
    fwPrefixToControllerPair n (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)) =
      prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair) := by
  rw [fwPrefixToControllerPair_diagonal]
  apply Fin.ext
  simp [prefixDiagonalPairIndex, finProdFinEquiv]

/-- The pair permutation is lifted independently within each stage, and
leaves each high/low endpoint orientation unchanged. -/
def fwPrefixToControllerInput (P n : ℕ) :
    Equiv.Perm ((Fin P × Fin (6 * (n + 8))) × Bool) where
  toFun x := ((x.1.1, fwPrefixToControllerPair n x.1.2), x.2)
  invFun x := ((x.1.1, (fwPrefixToControllerPair n).symm x.1.2), x.2)
  left_inv := by rintro ⟨⟨j,q⟩,side⟩; simp
  right_inv := by rintro ⟨⟨j,q⟩,side⟩; simp

/-- Stage-wise sums remain stage-wise after the physical pair reindexing. -/
theorem fw_controller_stage_sum {P n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin P → Fin (6 * (n + 8)) → A) (j : Fin P) :
    (∑ q, f j (fwPrefixToControllerPair n q)) = ∑ q, f j q := by
  exact Equiv.sum_comp (fwPrefixToControllerPair n) (f j)

/-- Squared physical pair-incidence invoices are preserved separately for
 each stage by the network-major to block-major reindexing. -/
theorem fw_controller_stage_squared_invoice {P n : ℕ}
    (cells : (Fin P × Fin (6 * (n + 8))) × Bool → Cell n)
    (line : Cell n → Prop) [DecidablePred line] (j : Fin P) :
    (∑ q, (physicalPairLineWeight cells line (j, fwPrefixToControllerPair n q)) ^ 2) =
      ∑ q, (physicalPairLineWeight cells line (j, q)) ^ 2 := by
  exact fw_controller_stage_sum (fun j q => (physicalPairLineWeight cells line (j,q)) ^ 2) j


/-- After reindexing, a diagonal tag names the original bridge rectangle
and its correctly oriented pair corners. -/
theorem fw_bridge_reindexed_diagonal_cell {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (rect : Fin (4 * 6)) (pair : Fin 2) (side : Bool) :
    fwBridgePhysicalPairCells hrect hs choice rows cols hr hc
      ((j, fwPrefixToControllerPair n
        (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair))), side) =
      packedRectangleCorner hs choice
        (bridgeDiagonalRectangle hrect (finProdFinEquiv (j,rect)), prefixPairCorner pair side) := by
  rw [fwPrefixToControllerPair_diagonal]
  let idx := ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
    (finProdFinEquiv (Fin.castLE (by omega : 4 * 6 ≤ 3 * (n + 8)) rect,pair))),side)
  let role : (Fin (5 * (4 * 6)) × Fin 4) ⊕ ((Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) :=
    Sum.inl (finProdFinEquiv (j,rect), prefixPairCorner pair side)
  have hrole : fwBridgePairCellEquiv n idx = role := by
    apply (Equiv.ofBijective (fwBridgeControllerSlot n) (fwBridgeControllerSlot_bijective n)).injective
    change fwBridgeControllerSlot n (fwBridgePairCellEquiv n idx) = fwBridgeControllerSlot n role
    simp only [fwBridgePairCellEquiv, Equiv.trans_apply, Equiv.ofBijective_apply_symm_apply]
    dsimp [idx,role,fwBridgeControllerSlot,fwBridgeDiagonalSlot]
    rw [fw_pair_controller_slot, bridgeDiagonalBlockSelect_at]
  change fwBridgePhysicalCells hrect hs choice rows cols hr hc (fwBridgePairCellEquiv n idx) = _
  rw [hrole]
  rfl


/-- After reindexing, an ordinary bridge tag names its actual network cell. -/
theorem fw_bridge_reindexed_ordinary_cell {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (network : Fin 2) (edge : Fin 3 × Fin n) (side : Bool) :
    fwBridgePhysicalPairCells hrect hs choice rows cols hr hc
      ((j, fwPrefixToControllerPair n
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,edge))), side) =
      fwBridgeLayerCells rows cols hr hc ((j,edge),(decide (network = 1),side)) := by
  rw [fwPrefixToControllerPair_ordinary]
  let idx := ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
    (finProdFinEquiv (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge,network))),side)
  let role : (Fin (5 * (4 * 6)) × Fin 4) ⊕ ((Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) :=
    Sum.inr ((j,edge),(decide (network = 1),side))
  have hrole : fwBridgePairCellEquiv n idx = role := by
    apply (Equiv.ofBijective (fwBridgeControllerSlot n) (fwBridgeControllerSlot_bijective n)).injective
    change fwBridgeControllerSlot n (fwBridgePairCellEquiv n idx) = fwBridgeControllerSlot n role
    simp only [fwBridgePairCellEquiv, Equiv.trans_apply, Equiv.ofBijective_apply_symm_apply]
    dsimp [idx,role,fwBridgeControllerSlot,fwBridgeOrdinarySlot,bridgeOrdinarySlot]
    rw [fw_pair_controller_slot]
    fin_cases network <;> cases side <;> rfl
  change fwBridgePhysicalCells hrect hs choice rows cols hr hc (fwBridgePairCellEquiv n idx) = _
  rw [hrole]
  rfl

/-- After reindexing, a diagonal tag names the original wide rectangle
and its correctly oriented pair corners. -/
theorem fw_wide_reindexed_diagonal_cell {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (rect : Fin (4 * 6)) (pair : Fin 2) (side : Bool) :
    fwWidePhysicalPairCells hwide hs choice rows cols hr hc
      ((j, fwPrefixToControllerPair n
        (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair))), side) =
      packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j,rect)), prefixPairCorner pair side) := by
  rw [fwPrefixToControllerPair_diagonal]
  let idx := ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
    (finProdFinEquiv (Fin.castLE (by omega : 4 * 6 ≤ 3 * (n + 8)) rect,pair))),side)
  let role : (Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4) ⊕ ((Fin (3 * (n / 450)) × (Fin 3 × Fin n)) × (Bool × Bool)) :=
    Sum.inl (finProdFinEquiv (j,rect), prefixPairCorner pair side)
  have hrole : fwWidePairCellEquiv n idx = role := by
    apply (Equiv.ofBijective (fwWideControllerSlot n) (fwWideControllerSlot_bijective n)).injective
    change fwWideControllerSlot n (fwWidePairCellEquiv n idx) = fwWideControllerSlot n role
    simp only [fwWidePairCellEquiv, Equiv.trans_apply, Equiv.ofBijective_apply_symm_apply]
    dsimp [idx,role,fwWideControllerSlot]
    rw [fw_pair_controller_slot, bridgeDiagonalBlockSelect_at]
  change fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWidePairCellEquiv n idx) = _
  rw [hrole]
  rfl


/-- After reindexing, an ordinary wide tag names its actual network cell. -/
theorem fw_wide_reindexed_ordinary_cell {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (network : Fin 2) (edge : Fin 3 × Fin n) (side : Bool) :
    fwWidePhysicalPairCells hwide hs choice rows cols hr hc
      ((j, fwPrefixToControllerPair n
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,edge))), side) =
      fwWideOrdinaryCells rows cols hr hc ((j,edge),(decide (network = 1),side)) := by
  rw [fwPrefixToControllerPair_ordinary]
  let idx := ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
    (finProdFinEquiv (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge,network))),side)
  let role : (Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4) ⊕ ((Fin (3 * (n / 450)) × (Fin 3 × Fin n)) × (Bool × Bool)) :=
    Sum.inr ((j,edge),(decide (network = 1),side))
  have hrole : fwWidePairCellEquiv n idx = role := by
    apply (Equiv.ofBijective (fwWideControllerSlot n) (fwWideControllerSlot_bijective n)).injective
    change fwWideControllerSlot n (fwWidePairCellEquiv n idx) = fwWideControllerSlot n role
    simp only [fwWidePairCellEquiv, Equiv.trans_apply, Equiv.ofBijective_apply_symm_apply]
    dsimp [idx,role,fwWideControllerSlot,bridgeOrdinarySlot]
    rw [fw_pair_controller_slot]
    fin_cases network <;> cases side <;> rfl
  change fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWidePairCellEquiv n idx) = _
  rw [hrole]
  rfl


/-- Ordinary controller slots are block-major: the network is the low
binary digit, after the first 48 diagonal pair slots. -/
theorem fwPrefixToControllerPair_ordinary_val (n : ℕ) (network : Fin 2) (edge : Fin 3 × Fin n) :
    (fwPrefixToControllerPair n (prefixOrdinaryPairIndex
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,edge))).val =
      48 + 2 * (finProdFinEquiv edge).val + network.val := by
  rw [fwPrefixToControllerPair_ordinary]
  simp [bridgeOrdinaryBlockIndex, finProdFinEquiv]
  omega

@[simp] theorem fwPrefixToControllerInput_stage (P n : ℕ)
    (j : Fin P) (q : Fin (6 * (n + 8))) (side : Bool) :
    (fwPrefixToControllerInput P n ((j,q),side)).1.1 = j := rfl

@[simp] theorem fwPrefixToControllerInput_side (P n : ℕ)
    (j : Fin P) (q : Fin (6 * (n + 8))) (side : Bool) :
    (fwPrefixToControllerInput P n ((j,q),side)).2 = side := rfl


/-- Stage-weighted squared-incidence invoices survive the reindexing without
mixing different stage widths. -/
theorem fw_controller_weighted_squared_invoice {P n : ℕ}
    (cells : (Fin P × Fin (6 * (n + 8))) × Bool → Cell n)
    (line : Cell n → Prop) [DecidablePred line] (width : Fin P → ℝ) :
    (∑ j, (width j) ^ 2 * ∑ q,
      (physicalPairLineWeight cells line (j, fwPrefixToControllerPair n q)) ^ 2) =
    ∑ j, (width j) ^ 2 * ∑ q, (physicalPairLineWeight cells line (j, q)) ^ 2 := by
  simp_rw [fw_controller_stage_squared_invoice]

end
end Sude
