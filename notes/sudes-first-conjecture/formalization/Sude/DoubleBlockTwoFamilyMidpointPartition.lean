import Sude.DoubleBlockPhysicalMidpointPartition

/-! One exact midpoint partition for two physically disjoint grouped families.
Neither the remaining physical cells nor the remaining network slots vanish. -/
namespace Sude
noncomputable section

/-- Split the physical row and the supported network slots once, then cancel
matched variable gaps independently in each family. -/
theorem double_block_two_family_midpoint_partition {n P₁ P₂ B₁ B₂ : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    (cells₁ : (Fin P₁ × Fin B₁ × Fin 2) × Bool → Cell n)
    (cells₂ : (Fin P₂ × Fin B₂ × Fin 2) × Bool → Cell n)
    (hcells₁ : Function.Injective cells₁) (hcells₂ : Function.Injective cells₂)
    (hdisj : Disjoint (Finset.univ.image cells₁) (Finset.univ.image cells₂))
    (old new : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs K new) (network : CenteredNetwork E K v)
    (T₁ T₂ : Finset K)
    (hT₁ : T₁ ⊆ Finset.univ.biUnion network.block)
    (hT₂ : T₂ ⊆ Finset.univ.biUnion network.block) (hTdisj : Disjoint T₁ T₂)
    (ι₁ : K → Fin P₁ × Fin B₁ × Fin 2) (ι₂ : K → Fin P₂ × Fin B₂ × Fin 2)
    (hinj₁ : Set.InjOn ι₁ (↑T₁ : Set K)) (hinj₂ : Set.InjOn ι₂ (↑T₂ : Set K))
    (r : Fin n)
    (hmatch₁ : ∀ k ∈ T₁, cells₁ (ι₁ k,false) = (v.low k,v.column k) ∧
      cells₁ (ι₁ k,true) = (v.high k,v.column k))
    (hmatch₂ : ∀ k ∈ T₂, cells₂ (ι₂ k,false) = (v.low k,v.column k) ∧
      cells₂ (ι₂ k,true) = (v.high k,v.column k)) :
    let A₁ := Finset.univ.image cells₁
    let A₂ := Finset.univ.image cells₂
    let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion network.block
    let line := fun c : Cell n => c.1 = r
    let gap₁ := fun i => (entry new (cells₁ (i,true)) : ℝ) - entry new (cells₁ (i,false))
    let gap₂ := fun i => (entry new (cells₂ (i,true)) : ℝ) - entry new (cells₂ (i,false))
    (physicalNetworkMidpointTwice v network r : ℝ) =
      (2 * doubleBlockActualCenteredScore cells₁ line old new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight cells₁ line j b * doubleStageMidpointMean cells₁ old j) +
        ∑ i ∈ Finset.univ \ T₁.image ι₁, gap₁ i * physicalPairLineOrientation cells₁ line i) +
      (2 * doubleBlockActualCenteredScore cells₂ line old new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight cells₂ line j b * doubleStageMidpointMean cells₂ old j) +
        ∑ i ∈ Finset.univ \ T₂.image ι₂, gap₂ i * physicalPairLineOrientation cells₂ line i) +
      2 * (∑ c ∈ row \ (A₁ ∪ A₂), (entry new c : ℝ)) +
      ∑ k ∈ U \ (T₁ ∪ T₂), (rowNetworkDelta v k r : ℝ) := by
  classical
  dsimp only
  let A₁ := Finset.univ.image cells₁
  let A₂ := Finset.univ.image cells₂
  let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
  let line := fun c : Cell n => c.1 = r
  have hT : T₁ ∪ T₂ ⊆ Finset.univ.biUnion network.block := Finset.union_subset hT₁ hT₂
  have hpartition := physical_network_midpoint_selected_partition v network (A₁ ∪ A₂) (T₁ ∪ T₂) hT r
  dsimp only at hpartition
  have hline : row ∩ (A₁ ∪ A₂) = A₁.filter line ∪ A₂.filter line := by
    ext ⟨i,j⟩
    simp [row, line, and_or_left, and_comm, eq_comm]
  have hfilters : Disjoint (A₁.filter line) (A₂.filter line) :=
    hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h₁ := double_block_selected_row_matched_cancellation cells₁ hcells₁ old new v T₁ ι₁ hinj₁ r hmatch₁
  have h₂ := double_block_selected_row_matched_cancellation cells₂ hcells₂ old new v T₂ ι₂ hinj₂ r hmatch₂
  dsimp only at h₁ h₂
  change (physicalNetworkMidpointTwice v network r : ℝ) =
    2 * (∑ c ∈ row ∩ (A₁ ∪ A₂), (entry new c : ℝ)) +
    2 * (∑ c ∈ row \ (A₁ ∪ A₂), (entry new c : ℝ)) +
    (∑ k ∈ T₁ ∪ T₂, (rowNetworkDelta v k r : ℝ)) +
    ∑ k ∈ Finset.univ.biUnion network.block \ (T₁ ∪ T₂), (rowNetworkDelta v k r : ℝ) at hpartition
  rw [hline, Finset.sum_union hfilters, Finset.sum_union hTdisj] at hpartition
  linarith

end
end Sude
