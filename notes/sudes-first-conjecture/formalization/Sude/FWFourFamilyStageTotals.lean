import Sude.FWFourFamilyPairInjection
import Sude.CombinedPhysicalStageFamilies

/-! Four-family stage reindexing and exact physical stage totals. -/
namespace Sude
noncomputable section
abbrev FWFourStageIndex (n P : ℕ) := ((Fin 5 ⊕ Fin 16) ⊕ Fin (3 * (n / 450))) ⊕ Fin P

def fwFourStageInputEquiv (n P : ℕ) :
    ((FWFourStageIndex n P × Fin (6 * (n + 8))) × Bool) ≃ FWFourFamilyPairInputs n P where
  toFun x := match x with
    | ((Sum.inl (Sum.inl (Sum.inl j)), i), b) => Sum.inl (Sum.inl (Sum.inl ((j, i), b)))
    | ((Sum.inl (Sum.inl (Sum.inr j)), i), b) => Sum.inl (Sum.inl (Sum.inr ((j, i), b)))
    | ((Sum.inl (Sum.inr j), i), b) => Sum.inl (Sum.inr ((j, i), b))
    | ((Sum.inr j, i), b) => Sum.inr ((j, i), b)
  invFun x := match x with
    | Sum.inl (Sum.inl (Sum.inl ((j, i), b))) => ((Sum.inl (Sum.inl (Sum.inl j)), i), b)
    | Sum.inl (Sum.inl (Sum.inr ((j, i), b))) => ((Sum.inl (Sum.inl (Sum.inr j)), i), b)
    | Sum.inl (Sum.inr ((j, i), b)) => ((Sum.inl (Sum.inr j), i), b)
    | Sum.inr ((j, i), b) => ((Sum.inr j, i), b)
  left_inv := by
    rintro ⟨⟨(((j | j) | j) | j), i⟩, b⟩ <;> rfl
  right_inv := by
    rintro ((((⟨⟨j, i⟩, b⟩ | ⟨⟨j, i⟩, b⟩) | ⟨⟨j, i⟩, b⟩) | ⟨⟨j, i⟩, b⟩)) <;> rfl

theorem fw_four_stage_reindex {n P : ℕ} (f : FWFourFamilyPairInputs n P → Cell n) (hi : Function.Injective f) :
    Function.Injective (f ∘ fwFourStageInputEquiv n P) ∧
    Finset.univ.image (f ∘ fwFourStageInputEquiv n P) = Finset.univ.image f := by
  classical
  constructor
  · exact hi.comp (fwFourStageInputEquiv n P).injective
  · rw [← Finset.image_image, Finset.image_univ_of_surjective (fwFourStageInputEquiv n P).surjective]

/-- General finite stage set, using the existing Fin-indexed stage API. -/
def finiteStageFinCells {n Q : ℕ} {I : Type*} [Fintype I] (cells : (I × Fin Q) × Bool → Cell n) :
    (Fin (Fintype.card I) × Fin Q) × Bool → Cell n :=
  fun x => cells (((Fintype.equivFin I).symm x.1.1, x.1.2), x.2)

theorem finite_physical_pair_stage_totals {n Q : ℕ} {I : Type*} [Fintype I]
    (hQ : 0 < Q) (a : Cell n ≃ Fin (n * n))
    (cells : (I × Fin Q) × Bool → Cell n) (hi : Function.Injective cells) :
    let e := Fintype.equivFin I
    let finCells := finiteStageFinCells cells
    let stages := fun j : I => physicalPairStageCells finCells (e j)
    let means := fun j : I => physicalStageMidpointAverage a finCells (e j)
    Set.PairwiseDisjoint (Set.univ : Set I) stages ∧
    (∀ j, (stages j).card = 2 * Q) ∧
    (∀ j, (∑ c ∈ stages j, (entry a c : ℝ)) = ((2 * Q : ℕ) : ℝ) * means j) ∧
    Finset.univ.biUnion stages = Finset.univ.image cells := by
  classical
  dsimp only
  let e := Fintype.equivFin I
  let finCells := finiteStageFinCells cells
  let stages := fun j : I => physicalPairStageCells finCells (e j)
  have hf : Function.Injective finCells := by
    rintro ⟨⟨j, i⟩, s⟩ ⟨⟨j', i'⟩, s'⟩ heq
    have h := hi heq
    have hj : e.symm j = e.symm j' := congrArg (fun x => x.1.1) h
    have hii : i = i' := congrArg (fun x => x.1.2) h
    have hs : s = s' := congrArg Prod.snd h
    cases e.symm.injective hj
    cases hii
    cases hs
    rfl
  have hd := physical_pair_stage_cells_disjoint_card finCells hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j _ k _ hjk
    exact hd.1 (Set.mem_univ (e j)) (Set.mem_univ (e k)) (fun h => hjk (e.injective h))
  · intro j
    exact hd.2 (e j)
  · intro j
    exact physical_pair_stage_sum_midpoint_average hQ a finCells hf (e j)
  · ext c
    simp only [physicalPairStageCells, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, ⟨⟨i, s⟩, h⟩⟩
      exact ⟨((j, i), s), by simpa [stages, physicalPairStageCells, finCells, finiteStageFinCells, e] using h⟩
    · rintro ⟨⟨⟨j, i⟩, s⟩, h⟩
      refine ⟨j, ⟨(i, s), ?_⟩⟩
      simpa [stages, physicalPairStageCells, finCells, finiteStageFinCells, e] using h



/-- All four FW families, indexed by their original stage labels, yield
pairwise-disjoint physical stages with exact sizes and actual midpoint sums. -/
theorem fw_four_family_stage_totals {n P : ℕ}
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n * n)) :
    let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    let cells := f ∘ fwFourStageInputEquiv n P
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let stages := fun j : FWFourStageIndex n P =>
      Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool => cells ((j, x.1), x.2))
    let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    Function.Injective cells ∧ Finset.univ.image cells = roles ∧
    Set.PairwiseDisjoint (Set.univ : Set (FWFourStageIndex n P)) stages ∧
    (∀ j, (stages j).card = 12 * (n + 8)) ∧
    (∀ j, (∑ c ∈ stages j, (entry a c : ℝ)) = ((12 * (n + 8) : ℕ) : ℝ) * means j) ∧
    Finset.univ.biUnion stages = roles := by
  classical
  dsimp only
  let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  let cells := f ∘ fwFourStageInputEquiv n P
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  have hf := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hf
  have hc := fw_four_stage_reindex f hf.1
  have himage : Finset.univ.image cells = roles := hc.2.trans hf.2
  have ht := finite_physical_pair_stage_totals (show 0 < 6 * (n + 8) by omega) a cells hc.1
  dsimp only at ht
  simp only [physicalPairStageCells, physicalStageMidpointAverage, finiteStageFinCells,
    Equiv.symm_apply_apply] at ht
  have hQ : 2 * (6 * (n + 8)) = 12 * (n + 8) := by omega
  rw [hQ] at ht
  exact ⟨hc.1, himage, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.trans himage⟩

end
end Sude
