import Sude.FWGrowthPackedSuffix
import Sude.FWGrowthChoiceRetraction
import Sude.BTGrowingOffsetPhysical

/-! Extract the growth geometry and same-square trace placement from the
joint theta-witness interfaces. This does not construct a theta witness or
perform the growth reallocation. -/
namespace Sude
noncomputable section

/-- The realized growth suffix inherits both joint packings, and the exact
nested maximum-stage rectangle choice has the required balanced values on
all realized growth rectangles. The reservations and original choice remain
unchanged. -/
theorem fw_theta_growth_suffix_geometry {n L P M : ℕ}
    (hrect : 5*(4*6) ≤ L) (hseed : 5*(4*6)+16*(4*6) ≤ L)
    (hwide : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6) ≤ L)
    (hmax : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+M*(4*6) ≤ L)
    (hoff : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+P*(4*6) ≤ L)
    (hle : P ≤ M) (hs : 2*L+1 ≤ n) (other : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n)) :
    let choice := fwBridgeSeedRectangleChoice hrect hseed
      (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax other))
    LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr) →
    LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc) →
    LayerPacking.PackedLayers (packedRectangleSupport hs choice) gr ∧
    LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) gc ∧
    (∀ (j : Fin P) (rect : Fin (4*6)),
      choice (btGrowingOffsetRectangle
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff (finProdFinEquiv (j,rect))) =
        decide (rect.val < 12)) := by
  classical
  dsimp only
  intro hrows hcols
  refine ⟨LayerPacking.packed_layers_suffix _ _ hrows,
    LayerPacking.packed_layers_suffix _ _ hcols, ?_⟩
  intro j rect
  let prior := fwBridgeSeedRectangleChoice hrect hseed
    (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax other))
  have hretract : fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff prior = prior :=
    fw_theta_witness_choice_retract_realized hrect hseed hwide hmax hoff hle other
  have hchoice := fwBridgeSeedWideGrowthChoice_growth hrect hseed hwide hoff prior j rect
  rw [hretract] at hchoice
  simpa only [prior, fwGrowthRectangle, btGrowingOffsetRectangle] using hchoice

/-- The growth trace initial stock in the theta witness is a subset of the
actual prescribed pool, independently of which early values were removed. -/
theorem fw_theta_growth_initial_subset_pool (n : ℕ) (early : Finset ℕ) :
    ∀ p ∈ ((poolFinset n).filter (fun p => 43 < p)) \ early, p ∈ pool n := by
  intro p hp
  exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1

/-- If a later square preserves all physical growth-role cells of the
trace-placed source square, the identical trace placement holds there. -/
theorem fw_growth_trace_placement_of_preserved_roles
    {n L : ℕ} {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (grown new : Cell n ≃ Fin (n*n))
    (hpres : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        entry grown (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry grown (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput (by omega) (by omega) x)).val) :
    ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry new (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput (by omega) (by omega) x)).val := by
  intro x
  exact (hpres x).trans (hplaced x)

end
end Sude
