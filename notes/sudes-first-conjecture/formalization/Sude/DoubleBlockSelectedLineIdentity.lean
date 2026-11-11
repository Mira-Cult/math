import Sude.DoubleBlockProtectedLogReallocation
import Sude.PhysicalVariableGapCancellation

/-! Exact selected-line bookkeeping for grouped physical pairs, including
variable gap orientations. No concentration or full-line bound is asserted. -/
namespace Sude
noncomputable section

/-- The actual selected-cell line sum equals the centered midpoint score,
source-stage mean contributions and the signed actual half-gap terms. -/
theorem double_block_actual_selected_line_identity {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (hcells : Function.Injective cells)
    (line : Cell n → Prop) [DecidablePred line]
    (old new : Cell n ≃ Fin (n*n)) :
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry new c : ℝ)) =
      doubleBlockActualCenteredScore cells line old new +
      (∑ j, ∑ b, doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j) +
      ∑ j, ∑ b, ∑ p, physicalPairLineOrientation cells line (j,b,p) *
        (((entry new (cells ((j,b,p),true)) : ℝ) - entry new (cells ((j,b,p),false))) / 2) := by
  classical
  have hline := physicalPair_line_sum_midpoint cells hcells line new
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib] at hline
  unfold doubleBlockActualCenteredScore
  simp only [Finset.sum_sub_distrib, doubleBlockPairMidpoint]
  linarith

/-- On a supplied physical row network, matched selected pair orientations
cancel their corresponding network corrections. All unmatched actual-gap
orientations remain, including any rectangle and perpendicular-network pairs. -/
theorem double_block_selected_row_matched_cancellation {n P B : ℕ} {K : Type*} [DecidableEq K]
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (hcells : Function.Injective cells) (old new : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs K new) (T : Finset K) (ι : K → Fin P × Fin B × Fin 2)
    (hinj : Set.InjOn ι (↑T : Set K)) (r : Fin n)
    (hmatch : ∀ k ∈ T, cells (ι k, false) = (v.low k, v.column k) ∧
      cells (ι k, true) = (v.high k, v.column k)) :
    let gap := fun i => (entry new (cells (i,true)) : ℝ) - entry new (cells (i,false))
    let line := fun c : Cell n => c.1 = r
    2 * (∑ c ∈ (Finset.univ.image cells).filter line, (entry new c : ℝ)) +
      (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) =
    2 * doubleBlockActualCenteredScore cells line old new +
      2 * (∑ j, ∑ b, doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j) +
      ∑ i ∈ Finset.univ \ T.image ι, gap i * physicalPairLineOrientation cells line i := by
  classical
  dsimp only
  let line := fun c : Cell n => c.1 = r
  let gap := fun i => (entry new (cells (i,true)) : ℝ) - entry new (cells (i,false))
  let orient := fun i => gap i * physicalPairLineOrientation cells line i
  have hselected := double_block_actual_selected_line_identity cells hcells line old new
  have hdelta := physical_network_matched_variable_gap_delta_sum v cells T ι hinj r gap hmatch (by
    intro k hk; rfl)
  have hsplit : (∑ i : Fin P × Fin B × Fin 2, orient i) =
      (∑ i ∈ T.image ι, orient i) + ∑ i ∈ Finset.univ \ T.image ι, orient i := by
    symm
    simpa only [add_comm] using Finset.sum_sdiff (f := orient) (Finset.subset_univ (T.image ι))
  have horient : 2 * (∑ j, ∑ b, ∑ p, physicalPairLineOrientation cells line (j,b,p) *
      (((entry new (cells ((j,b,p),true)) : ℝ) - entry new (cells ((j,b,p),false))) / 2)) =
      ∑ i : Fin P × Fin B × Fin 2, orient i := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    dsimp [orient, gap]
    ring
  change 2 * (∑ c ∈ (Finset.univ.image cells).filter line, (entry new c : ℝ)) +
      (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) =
    2 * doubleBlockActualCenteredScore cells line old new +
      2 * (∑ j, ∑ b, doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j) +
      ∑ i ∈ Finset.univ \ T.image ι, orient i
  linarith

end
end Sude
