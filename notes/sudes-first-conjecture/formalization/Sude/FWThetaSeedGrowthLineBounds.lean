import Sude.FWSeedOrderedAllLineAdapter
import Sude.FWGrowthOrderedStageLineBound

/-! The supplied theta-style seed and growth fields yield the physical
component interfaces on the same ordered square. No score or witness existence,
whole-line bound, completion or later flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000

/-- Translate the supplied all-line seed invoice and the row/column growth
midpoint invoices to the actual four-family stage-mean interfaces. -/
theorem fw_theta_seed_growth_line_interfaces
    {n L : ℕ} {initial remaining : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius remaining last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hrect : 5 * (4*6) ≤ L) (hseed : 5*(4*6) + 16*(4*6) ≤ L)
    (hwide : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) ≤ L)
    (hoff : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) + stages.length*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (hgr : gr.length = stages.length*3) (hgc : gc.length = stages.length*3)
    (grown ordered : Cell n ≃ Fin (n*n))
    (ωseed : Fin 16 → Equiv.Perm (Fin (6*(n+8))))
    (τ : Fin stages.length → Equiv.Perm (Fin (6*(n+8)))) (U V : ℝ)
    (hseedPlace : ∀ j i side,
      entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),side)) =
        entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,ωseed j i),side)))
    (hseedScore : ∀ l : Fin ((n+n)+2),
      let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      let line := fun z => z ∈ physicalAllLineCells l
      let value := fun j i => (((entry grown (seed ((j,i),false)) : ℝ) +
        entry grown (seed ((j,i),true))) / 2)
      |(∑ z ∈ (Finset.univ.image seed).filter line, (entry ordered z : ℝ)) -
        (∑ j, ((∑ i, physicalPairLineWeight seed line (j,i)) *
          ((∑ i, value j i) / ((6*(n+8) : ℕ) : ℝ)))) -
        (∑ p, physicalPairLineOrientation seed line p * ((2 : ℝ)/2))| ≤ U)
    (hgrowthPlace : ∀ x,
      entry ordered (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues rfl hpool (stagePairPermutation τ x)).val)
    (hgrowthRow : ∀ r : Fin n,
      let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
      let mean := fun j : Fin stages.length =>
        (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ)
      |∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.1 = r) p *
        ((((entry ordered (growth (p,true)) : ℝ) + entry ordered (growth (p,false))) / 2) - mean p.1)| ≤ V)
    (hgrowthCol : ∀ c : Fin n,
      let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
      let mean := fun j : Fin stages.length =>
        (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ)
      |∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.2 = c) p *
        ((((entry ordered (growth (p,true)) : ℝ) + entry ordered (growth (p,false))) / 2) - mean p.1)| ≤ V) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
    let mean := fun j : FWFourStageIndex n stages.length =>
      (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
        ((6*(n+8) : ℕ) : ℝ)
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
    (∀ r : Fin n,
      |(∑ z ∈ rowCells r ∩ Finset.univ.image seed, (entry ordered z : ℝ)) -
        (∑ j : Fin 16, ∑ i : Fin (6*(n+8)), physicalPairLineWeight seed (fun z => z ∈ rowCells r) (j,i) *
          mean (Sum.inl (Sum.inl (Sum.inr j))))| ≤ U) ∧
    (∀ c : Fin n,
      |(∑ z ∈ columnCells c ∩ Finset.univ.image seed, (entry ordered z : ℝ)) -
        (∑ j : Fin 16, ∑ i : Fin (6*(n+8)), physicalPairLineWeight seed (fun z => z ∈ columnCells c) (j,i) *
          mean (Sum.inl (Sum.inl (Sum.inr j))))| ≤ U) ∧
    (∀ r : Fin n,
      |(∑ z ∈ rowCells r ∩ Finset.univ.image growth, (entry ordered z : ℝ)) -
        (∑ j : Fin stages.length, ∑ i : Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z ∈ rowCells r) (j,i) * mean (Sum.inr j))| ≤ V) ∧
    (∀ c : Fin n,
      |(∑ z ∈ columnCells c ∩ Finset.univ.image growth, (entry ordered z : ℝ)) -
        (∑ j : Fin stages.length, ∑ i : Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z ∈ columnCells c) (j,i) * mean (Sum.inr j))| ≤ V) := by
  classical
  have hseedBound := fw_seed_ordered_stage_line_bound_of_all_lines hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc grown ordered ωseed U hseedPlace hseedScore
  have hgrowthBound := fw_growth_ordered_stage_line_bound trace hpool hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ordered τ hgrowthPlace V hgrowthRow hgrowthCol
  dsimp only at hseedBound hgrowthBound ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    have h := hseedBound.1 r
    simpa only [← mem_rowCells, Finset.filter_mem_eq_inter, Finset.inter_comm] using h
  · intro c
    have h := hseedBound.2 c
    simpa only [← mem_columnCells, Finset.filter_mem_eq_inter, Finset.inter_comm] using h
  · intro r
    have h := hgrowthBound.2.1 r
    have hp : (fun z : Cell n => z.1 = r) = (fun z => z ∈ rowCells r) := by
      funext z; exact propext (mem_rowCells r z).symm
    rw [hp, Fintype.sum_prod_type] at h
    exact h
  · intro c
    have h := hgrowthBound.2.2 c
    have hp : (fun z : Cell n => z.2 = c) = (fun z => z ∈ columnCells c) := by
      funext z; exact propext (mem_columnCells c z).symm
    rw [hp, Fintype.sum_prod_type] at h
    exact h

end
end Sude
