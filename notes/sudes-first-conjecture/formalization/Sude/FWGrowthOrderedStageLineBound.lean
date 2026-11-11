import Sude.FWGrowthFourStageMean
import Sude.FWGrowthTracePhysicalEntryBound

/-! Growth physical-line discrepancy on the same trace-placed ordered square,
using the original four-family physical stage means. No conclusion is made
about other cells, a complete line, or a later switched square. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

/-- Supplied centered growth-midpoint bounds become physical growth-component
line bounds about the actual four-family stage means. The trace placement
preserves each stage occurrence and its own (possibly different) signed gap. -/
theorem fw_growth_ordered_stage_line_bound {n L : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (a : Cell n ≃ Fin (n*n)) (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (hplaced : ∀ x, entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
      (trace.poolValues rfl hpool (stagePairPermutation ω x)).val)
    (B : ℝ)
    (hrow : ∀ r : Fin n,
      let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
      let μ := fun j : Fin stages.length =>
        (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ)
      |∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight cells (fun c => c.1 = r) p *
        ((((entry a (cells (p,true)) : ℝ) + entry a (cells (p,false))) / 2) - μ p.1)| ≤ B)
    (hcol : ∀ c : Fin n,
      let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
      let μ := fun j : Fin stages.length =>
        (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ)
      |∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight cells (fun z => z.2 = c) p *
        ((((entry a (cells (p,true)) : ℝ) + entry a (cells (p,false))) / 2) - μ p.1)| ≤ B) :
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
    let mean := fun j : FWFourStageIndex n stages.length =>
      (∑ i, (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2)) /
        ((6*(n+8) : ℕ) : ℝ)
    (∀ j : Fin stages.length, mean (Sum.inr j) =
      (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ)) ∧
    (∀ r : Fin n, |(∑ z ∈ rowCells r ∩ Finset.univ.image growth, (entry a z : ℝ)) -
      (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.1 = r) p * mean (Sum.inr p.1))| ≤ B) ∧
    (∀ c : Fin n, |(∑ z ∈ columnCells c ∩ Finset.univ.image growth, (entry a z : ℝ)) -
      (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.2 = c) p * mean (Sum.inr p.1))| ≤ B) := by
  classical
  dsimp only
  let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
  let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice gr gc hgr hgc
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
  let mean := fun j : FWFourStageIndex n stages.length =>
    (∑ i, (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2)) /
      ((6*(n+8) : ℕ) : ℝ)
  let μ := fun j : Fin stages.length =>
    (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ)
  have hmean (j : Fin stages.length) : mean (Sum.inr j) = μ j :=
    fw_four_family_growth_stage_mean trace hpool hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc a ω hplaced j
  have hphys := fw_growth_trace_midpoint_to_physical_lines trace hpool offset hoff hs choice gr gc hgr hgc
    a ω hplaced μ B hrow hcol
  dsimp only at hphys
  refine ⟨hmean, ?_, ?_⟩
  · intro r
    have hsplit := Finset.sum_sdiff (f := fun z => (entry a z : ℝ)) (Finset.inter_subset_left : rowCells r ∩ Finset.univ.image growth ⊆ rowCells r)
    have hset : rowCells r \ (rowCells r ∩ Finset.univ.image growth) = rowCells r \ Finset.univ.image growth := by ext z; simp
    rw [hset] at hsplit
    have hscore : (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.1 = r) p * mean (Sum.inr p.1)) =
        ∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.1 = r) p * μ p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hmean]
    rw [hscore]
    have hh := hphys.1 r
    have heq : (∑ z ∈ rowCells r ∩ Finset.univ.image growth, (entry a z : ℝ)) -
        (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.1 = r) p * μ p.1) =
        ((∑ z ∈ rowCells r, (entry a z : ℝ)) - (∑ z ∈ rowCells r \ Finset.univ.image growth, (entry a z : ℝ)) -
        (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.1 = r) p * μ p.1)) := by linarith
    rw [heq]
    exact hh
  · intro c
    have hsplit := Finset.sum_sdiff (f := fun z => (entry a z : ℝ)) (Finset.inter_subset_left : columnCells c ∩ Finset.univ.image growth ⊆ columnCells c)
    have hset : columnCells c \ (columnCells c ∩ Finset.univ.image growth) = columnCells c \ Finset.univ.image growth := by ext z; simp
    rw [hset] at hsplit
    have hscore : (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.2 = c) p * mean (Sum.inr p.1)) =
        ∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.2 = c) p * μ p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hmean]
    rw [hscore]
    have hh := hphys.2 c
    have heq : (∑ z ∈ columnCells c ∩ Finset.univ.image growth, (entry a z : ℝ)) -
        (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.2 = c) p * μ p.1) =
        ((∑ z ∈ columnCells c, (entry a z : ℝ)) - (∑ z ∈ columnCells c \ Finset.univ.image growth, (entry a z : ℝ)) -
        (∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.2 = c) p * μ p.1)) := by linarith
    rw [heq]
    exact hh

end
end Sude
