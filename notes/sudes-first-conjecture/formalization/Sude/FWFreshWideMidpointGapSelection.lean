import Sude.JointStageMidpointGapSelection
import Sude.DoubleBlockMidpointFailureBound
import Sude.FWWideSignedGapSlots
import Sude.FWWideSourceGapInterval
import Sude.FWPhysicalDoubleBlockGaps

/-! A fresh simultaneous wide-block selection. The midpoint and signed-gap
bounds use the same stage permutations and swaps. This is not an assertion
about any previously selected witness, spare values, or prime targets. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance freshWidePermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The supplied matched blocks, physical placement and midpoint invoice give
one fresh joint sample with both the midpoint and wide signed-gap bounds. -/
theorem fw_fresh_wide_midpoint_gap_selection {n L m : ℕ}
    (hn : 450 ≤ n) (hm : 0 < m)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3)
    (hc : cols.length = (3 * (n / 450)) * 3)
    (μ X : ℝ) (hX : (100 : ℝ) ≤ X)
    (hmlo : (243/500 : ℝ)*X ≤ μ) (hmhi : μ ≤ (123/250 : ℝ)*X)
    (blocks : List DoublePair)
    (hlen : blocks.length = (3*(n/450))*(3*(n+8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)))
    (old : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : FWWideInputs n,
      entry old (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks
        (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (line : Fin m → Cell n → Prop) (V : ℝ) (hV : 0 < V)
    (lo hi : Fin (3*(n/450)) → ℝ)
    (hinterval : ∀ j b p,
      doubleBlockPairMidpoint (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc)
        old j b p ∈ Set.Icc (lo j) (hi j))
    (hinvoice : ∀ l, doubleBlockCombinedProxy
      (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc) (line l) lo hi ≤ V/4) :
    let cells := fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc
    let gap := fun j b => fwPermutedWideSourceGap blocks hlen (fun _ => Equiv.refl _) j b
    let E := Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)
    (∀ j b p, entry old (cells ((j,b,p),true)) =
      entry old (cells ((j,b,p),false)) + gap j b) ∧
    ∃ π swaps,
      (∀ l, |doubleBlockSampleScore cells (line l) old π swaps| < E) ∧
      |(1/2 : ℝ) * ((∑ j, ∑ b ∈ fwWideSignedGapSlots n true, (gap j (π j b) : ℝ)) -
        ∑ j, ∑ b ∈ fwWideSignedGapSlots n false, (gap j (π j b) : ℝ))| <
      2 * Real.sqrt ((3/2 : ℝ) * ((3*(n/450) : ℕ) : ℝ) * ((64/235 : ℝ)*X)^2 * Real.log 16) := by
  classical
  dsimp only
  have hW : 0 < 3*(n/450) := by
    have hd : 0 < n/450 := Nat.div_pos hn (by omega)
    omega
  have hB : 24 ≤ 3*(n+8) := by omega
  have hXpos : 0 < X := by linarith
  have hΔ : 0 < (64/235 : ℝ)*X := by positivity
  let cells := fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc
  let gap := fun j b => fwPermutedWideSourceGap blocks hlen (fun _ => Equiv.refl _) j b
  let E := Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)
  let bad := {z : (Fin (3*(n/450)) → Equiv.Perm (Fin (3*(n+8)))) ×
      ((Fin (3*(n/450)) × Fin (3*(n+8))) → Bool) |
    ∃ l, E ≤ |doubleBlockSampleScore cells (line l) old z.1 z.2|}
  have hmid : ((stagePermutationMeasure (3*(n/450)) (3*(n+8))).prod
      (uniformOn (Set.univ : Set ((Fin (3*(n/450)) × Fin (3*(n+8))) → Bool)))).real bad ≤ (1/2 : ℝ) := by
    exact double_block_log_midpoint_failure_bound (by omega) hm V hV cells line old lo hi hinterval hinvoice
  have hslots := fw_wide_signed_gap_slots_card_disjoint n
  have hcard : ∀ (side : Bool) (j : Fin (3*(n/450))),
      (fwWideSignedGapSlots n side).card = 12 := by
    intro side j
    cases side
    · exact hslots.2.1
    · exact hslots.1
  have hvals : ∀ j b, (gap j b : ℝ) ∈
      Set.Icc ((2/3 : ℝ)*X) (((2/3 : ℝ)+(64/235 : ℝ))*X) := by
    intro j b
    exact fw_wide_source_gap_interval μ X hX hmlo hmhi blocks hlen hmatched j b
  obtain ⟨π, swaps, hgood, hgap⟩ := joint_stage_midpoint_gap_selection hW hB
    ((64/235 : ℝ)*X) hΔ (fun side _ => fwWideSignedGapSlots n side) hcard
    (fun _ => hslots.2.2) (fun j b => (gap j b : ℝ))
    (fun _ => (2/3 : ℝ)*X) (fun _ => ((2/3 : ℝ)+(64/235 : ℝ))*X)
    (by intro j; ring) hvals bad hmid
  constructor
  · have hphysical := fw_wide_physical_selected_double_gap hwide hs choice rows cols hr hc
      blocks hlen _ _ hmatched old hplaced
    intro j b p
    simpa [cells, gap, fwPermutedWideSourceGap] using hphysical.2 j b p
  · refine ⟨π, swaps, ?_, ?_⟩
    · intro l
      exact lt_of_not_ge (fun h => hgood ⟨l,h⟩)
    · exact hgap

end
end Sude
