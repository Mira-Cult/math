import Sude.BTGrowingPoolValues

/-! Transport selected actual low endpoints to their exact within-stage pair
indices. This is label bookkeeping only; it does not move any cells. -/
namespace Sude
noncomputable section

/-- A family of selected actual low endpoints has an exact family of pair
indices, with stagewise images, cardinalities and disjointness preserved. -/
theorem bt_growth_selected_label_indices
    {g Q P : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial radius final last stages)
    (hlen : stages.length = P) {ι : Type*} [DecidableEq ι]
    (T : Fin P → ι → Finset ℕ)
    (hsub : ∀ j t, T j t ⊆ (BTStageTrace.stageAt stages hlen j).lows) :
    ∃ I : Fin P → ι → Finset (Fin Q),
      (∀ j t, (I j t).image (trace.lowAt hlen j) = T j t) ∧
      (∀ j t, (I j t).card = (T j t).card) ∧
      (∀ j t u, Disjoint (T j t) (T j u) → Disjoint (I j t) (I j u)) := by
  classical
  let I : Fin P → ι → Finset (Fin Q) := fun j t => Finset.univ.filter (fun i => trace.lowAt hlen j i ∈ T j t)
  have hinj : ∀ j, Function.Injective (trace.lowAt hlen j) := by
    intro j
    exact ((BTStageTrace.stageAt stages hlen j).lows.orderEmbOfFin
      (trace.stage_properties _ (BTStageTrace.stageAt_mem stages hlen j)).2.2.2.1).injective
  have himage : ∀ j t, (I j t).image (trace.lowAt hlen j) = T j t := by
    intro j t
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_filter.mp hi).2
    · intro hp
      have hpstage := hsub j t hp
      have hp' : p ∈ Set.range (trace.lowAt hlen j) := by
        have he := Finset.range_orderEmbOfFin (BTStageTrace.stageAt stages hlen j).lows
          (trace.stage_properties _ (BTStageTrace.stageAt_mem stages hlen j)).2.2.2.1
        change p ∈ Set.range ((BTStageTrace.stageAt stages hlen j).lows.orderEmbOfFin _) 
        rw [he]
        exact hpstage
      obtain ⟨i, rfl⟩ := hp'
      exact Finset.mem_image.mpr ⟨i, by simp [I, hp], rfl⟩
  refine ⟨I, himage, ?_, ?_⟩
  · intro j t
    have h := Finset.card_image_of_injective (I j t) (hinj j)
    rw [himage j t] at h
    exact h.symm
  · intro j t u hdis
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have hti := (Finset.mem_filter.mp hi).2
    have hui := (Finset.mem_filter.mp hi').2
    exact Finset.disjoint_left.mp hdis hti hui

end
end Sude
