import Sude.DoubleBlockSelectedLineIdentity

/-! Exact one-family physical midpoint partition. All unmatched pair
orientations, other cells and network corrections remain explicit. -/
namespace Sude
noncomputable section

/-- On one physical row, substitute the selected double-block score and the
matched variable-gap cancellation into the full midpoint partition. The row
complement contains all cells outside this one family, including other
families, spare corners and free cells. -/
theorem double_block_physical_midpoint_partition {n P B : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (hcells : Function.Injective cells) (old new : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs K new) (network : CenteredNetwork E K v)
    (T : Finset K) (hT : T ⊆ Finset.univ.biUnion network.block)
    (ι : K → Fin P × Fin B × Fin 2) (hinj : Set.InjOn ι (↑T : Set K))
    (r : Fin n)
    (hmatch : ∀ k ∈ T, cells (ι k, false) = (v.low k, v.column k) ∧
      cells (ι k, true) = (v.high k, v.column k)) :
    let A := Finset.univ.image cells
    let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion network.block
    let line := fun c : Cell n => c.1 = r
    let gap := fun i => (entry new (cells (i,true)) : ℝ) - entry new (cells (i,false))
    (physicalNetworkMidpointTwice v network r : ℝ) =
      2 * doubleBlockActualCenteredScore cells line old new +
      2 * (∑ j, ∑ b, doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j) +
      (∑ i ∈ Finset.univ \ T.image ι, gap i * physicalPairLineOrientation cells line i) +
      2 * (∑ c ∈ row \ A, (entry new c : ℝ)) +
      ∑ k ∈ U \ T, (rowNetworkDelta v k r : ℝ) := by
  classical
  dsimp only
  let A := Finset.univ.image cells
  let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
  let line := fun c : Cell n => c.1 = r
  have hline : row ∩ A = A.filter line := by
    ext c
    cases c with
    | mk i j => simp [row, line, and_comm, Prod.mk.injEq, eq_comm]
  have hpartition := physical_network_midpoint_selected_partition v network A T hT r
  dsimp only at hpartition
  change (physicalNetworkMidpointTwice v network r : ℝ) =
    2 * (∑ c ∈ row ∩ A, (entry new c : ℝ)) +
    2 * (∑ c ∈ row \ A, (entry new c : ℝ)) +
    (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) +
    ∑ k ∈ Finset.univ.biUnion network.block \ T, (rowNetworkDelta v k r : ℝ) at hpartition
  rw [hline] at hpartition
  have hselected := double_block_selected_row_matched_cancellation cells hcells old new v T ι hinj r hmatch
  dsimp only at hselected
  change 2 * (∑ c ∈ A.filter line, (entry new c : ℝ)) +
      (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) = _ at hselected
  linarith

end
end Sude
