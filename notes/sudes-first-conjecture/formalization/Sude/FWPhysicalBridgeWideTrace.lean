import Sude.FWEarlyGrowthPhysical
import Sude.FWBridgeGridGrowth
import Sude.FWBridgeOrdinaryPlacement

/-! Connect a supplied physical initial grid to the same installed FW bridge
and wide witnesses. Crossing of X/23 remains explicit; no line-sum theorem is
asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Preserving all earlier role cells preserves both the ordinary bridge
and every wide physical role. -/
theorem fw_preserved_bridge_wide_roles {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c) :
    (∀ x, entry grown (fwBridgeLayerCells rows cols hr hc x) =
      entry old (fwBridgeLayerCells rows cols hr hc x)) ∧
    (∀ x, entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      entry old (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x)) := by
  constructor
  · intro x
    apply hfixed
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)))
  · intro x
    apply hfixed
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)

/-- Each graph-edge slot of the actual nominal bridge batches has the
corresponding selected gap in the preserved square, in both orientations. -/
theorem fw_preserved_bridge_ordinary_gap {n L : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (j : Fin 5) (edge : Fin 3 × Fin n) (network : Bool) :
    let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
    let gap := selectedBridgeGap batches index j
    0 < gap ∧ 2 ∣ gap ∧
    entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, true))) =
      entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, false))) + gap := by
  dsimp only
  have hf := (fw_preserved_bridge_wide_roles hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc
    wr wc hwr hwc old grown hfixed).1
  rw [hf _, hf _, hplace _, hplace _]
  simpa [fwBridgeOrdinarySlot, bridgeOrdinarySlot] using
    fw_bridge_ordinary_endpoint_gap n ∅ batches hvalid j edge network

/-- At a fixed graph edge, the same five actual bridge batches extend any
supplied complete even grid through X once its radius reaches X/23. The
physical bridge pair equations are proved on the preserved square. The
initial grid's labels and crossing are explicit inputs. -/
theorem fw_physical_bridge_extends_grid {α : Type*} [DecidableEq α] {n L : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (edge : Fin 3 × Fin n) (network : Bool)
    (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial initialGap radius) (heven : 2 ∣ radius)
    (hcross : (poolMaximum n : ℝ) / 23 ≤ radius) :
    let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
    let next := radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
    CompleteEvenGrid
      (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.range 5).image (Sum.inr : ℕ → Sum α ℕ))
      (joinedBridgeGap initialGap batches index) next ∧
    (poolMaximum n : ℝ) ≤ next ∧
    (∀ j : Fin 5, entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, true))) =
      entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, false))) +
        selectedBridgeGap batches index j) := by
  dsimp only
  let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
  obtain ⟨hnew, hbound⟩ := fw_selected_bridge_batches_grow_grid n ∅ batches hvalid index
    initial initialGap radius hgrid heven hcross
  refine ⟨hnew, hbound, ?_⟩
  intro j
  exact (fw_preserved_bridge_ordinary_gap batches hvalid hrect hseed hwide hs choice rows cols hr hc
    sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace j edge network).2.2

/-- The physical endpoint cells for the actual selected wide blocks, using
the existing bijection between wide roles and flattened block slots. -/
def fwWideSequenceCells {n L : ℕ} (blocks : List DoublePair)
    (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) : Fin blocks.length × Fin 4 → Cell n := fun x =>
  fwWidePhysicalCells hwide hs choice wr wc hwr hwc
    ((Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)).symm
      (Fin.cast hlen x.1, x.2))

/-- All actual wide-block gap equations and numerical bounds transfer to
the same grown square when the early physical roles are fixed. -/
theorem fw_preserved_wide_block_gaps {n L : ℕ}
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hgap : let cells := fwWideSequenceCells blocks hlen hwide hs choice wr wc hwr hwc
      ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry old (cells (i, 1)) = entry old (cells (i, 0)) + gap ∧
        entry old (cells (i, 2)) = entry old (cells (i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) :
    let cells := fwWideSequenceCells blocks hlen hwide hs choice wr wc hwr hwc
    ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
      entry grown (cells (i, 1)) = entry grown (cells (i, 0)) + gap ∧
      entry grown (cells (i, 2)) = entry grown (cells (i, 3)) + gap ∧
      (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n := by
  dsimp only at hgap ⊢
  have hf := (fw_preserved_bridge_wide_roles hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc
    wr wc hwr hwc old grown hfixed).2
  intro i
  obtain ⟨gap, hpos, heven, hpair1, hpair2, hlo, hhi⟩ := hgap i
  refine ⟨gap, hpos, heven, ?_, ?_, hlo, hhi⟩
  · dsimp only [fwWideSequenceCells]
    rw [hf, hf]
    exact hpair1
  · dsimp only [fwWideSequenceCells]
    rw [hf, hf]
    exact hpair2

end
end Sude
