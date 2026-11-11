import Sude.FWCanonicalFamilyLabelDisjoint

/-! One physical label per seed, growth, bridge and wide stage, for either
selected choice fiber. This is geometry only: no grid or gap assertion. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
local instance fwCanonicalFamilyRelabelStageDecidable : DecidableEq BTSelectedStage := Classical.decEq _

/-- Exact finite support of the source grid, including the five natural bridge tags. -/
def fwCanonicalFamilySourceSupport {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) :
    Finset (Sum (Sum (Sum (Fin 16) BTSelectedStage) ℕ) (Fin (3*(n/450)))) := by
  classical
  exact ((fwSeedTraceLabels f.stages).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.range 5).image Sum.inr).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

theorem fw_canonical_family_source_seed_mem {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (x : Sum (Fin 16) BTSelectedStage) :
    Sum.inl (Sum.inl x) ∈ fwCanonicalFamilySourceSupport f ↔ x ∈ fwSeedTraceLabels f.stages := by
  classical
  simp [fwCanonicalFamilySourceSupport]

theorem fw_canonical_family_source_bridge_mem {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (j : ℕ) :
    Sum.inl (Sum.inr j) ∈ fwCanonicalFamilySourceSupport f ↔ j < 5 := by
  classical
  simp [fwCanonicalFamilySourceSupport]

theorem fw_canonical_family_source_wide_mem {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (j : Fin (3*(n/450))) :
    Sum.inr j ∈ fwCanonicalFamilySourceSupport f := by
  classical
  simp [fwCanonicalFamilySourceSupport]

/-- The physical label associated to an actual tag in the source support. -/
def fwCanonicalFamilyLabel {n : ℕ} {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (x : {x // x ∈ fwCanonicalFamilySourceSupport f}) : Fin (fwJointRectangleCount n 254) := by
  classical
  rcases x with ⟨x, hx⟩
  cases x with
  | inl a =>
    cases a with
    | inl a =>
      exact fwCanonicalSeedGrowthLabel f side ⟨a, (fw_canonical_family_source_seed_mem f a).1 hx⟩
    | inr j =>
      exact bridgeDiagonalRectangle f.hrect
        (finProdFinEquiv (⟨j, (fw_canonical_family_source_bridge_mem f j).1 hx⟩, fwCanonicalChoiceRectangle side))
  | inr j =>
    exact fwWideRectangle f.hwide (finProdFinEquiv (j, fwCanonicalChoiceRectangle side))

/-- The exact source support embeds into the active choice fiber. -/
theorem fw_canonical_family_label_embedding {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (side : Bool) :
    Function.Injective (fwCanonicalFamilyLabel f side) ∧
    ∀ x, fwCanonicalFamilyLabel f side x ∈ fwActiveRectangleLabels n f.stages.length f.stageCap ∧
      fwSelectedThetaChoice hnlo otherChoice (fwCanonicalFamilyLabel f side x) = side := by
  classical
  constructor
  · intro a b h
    apply Subtype.ext
    rcases a with ⟨a,ha⟩
    rcases b with ⟨b,hb⟩
    cases a with
    | inl a =>
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          cases b with
          | inl b =>
            change fwCanonicalSeedGrowthLabel f side ⟨a, (fw_canonical_family_source_seed_mem f a).1 ha⟩ =
              fwCanonicalSeedGrowthLabel f side ⟨b, (fw_canonical_family_source_seed_mem f b).1 hb⟩ at h
            have he := fw_canonical_seed_growth_label_injective f side h
            exact congrArg (fun x => Sum.inl (Sum.inl x)) (congrArg Subtype.val he)
          | inr b =>
            exfalso
            exact fw_canonical_seed_growth_ne_bridge f side ⟨a, (fw_canonical_family_source_seed_mem f a).1 ha⟩
              ⟨b, (fw_canonical_family_source_bridge_mem f b).1 hb⟩ h
        | inr b =>
          exfalso
          exact fw_canonical_seed_growth_ne_wide f side ⟨a, (fw_canonical_family_source_seed_mem f a).1 ha⟩ b h
      | inr a =>
        cases b with
        | inl b =>
          cases b with
          | inl b =>
            exfalso
            exact fw_canonical_seed_growth_ne_bridge f side ⟨b, (fw_canonical_family_source_seed_mem f b).1 hb⟩
              ⟨a, (fw_canonical_family_source_bridge_mem f a).1 ha⟩ h.symm
          | inr b =>
            have hp := finProdFinEquiv.injective (bridgeDiagonalRectangle_injective f.hrect h)
            have hj := congrArg Fin.val (congrArg Prod.fst hp)
            exact congrArg (fun x => Sum.inl (Sum.inr x)) hj
        | inr b =>
          exfalso
          exact fw_canonical_bridge_ne_wide f side ⟨a, (fw_canonical_family_source_bridge_mem f a).1 ha⟩ b h
    | inr a =>
      cases b with
      | inl b =>
        cases b with
        | inl b =>
          exfalso
          exact fw_canonical_seed_growth_ne_wide f side ⟨b, (fw_canonical_family_source_seed_mem f b).1 hb⟩ a h.symm
        | inr b =>
          exfalso
          exact fw_canonical_bridge_ne_wide f side ⟨b, (fw_canonical_family_source_bridge_mem f b).1 hb⟩ a h.symm
      | inr b =>
        have hp := finProdFinEquiv.injective (fwWideRectangle_injective f.hwide h)
        exact congrArg Sum.inr (congrArg Prod.fst hp)
  · rintro ⟨x,hx⟩
    cases x with
    | inl a =>
      cases a with
      | inl a =>
        change fwCanonicalSeedGrowthLabel f side ⟨a, (fw_canonical_family_source_seed_mem f a).1 hx⟩ ∈
          fwActiveRectangleLabels n f.stages.length f.stageCap ∧
          fwSelectedThetaChoice hnlo otherChoice
            (fwCanonicalSeedGrowthLabel f side ⟨a, (fw_canonical_family_source_seed_mem f a).1 hx⟩) = side
        exact ⟨fw_canonical_seed_growth_label_mem f side _, fw_canonical_seed_growth_label_choice hnlo otherChoice f side _⟩
      | inr j =>
        let jj : Fin 5 := ⟨j, (fw_canonical_family_source_bridge_mem f j).1 hx⟩
        have hmem : bridgeDiagonalRectangle f.hrect (finProdFinEquiv (jj, fwCanonicalChoiceRectangle side)) ∈
            fwActiveRectangleLabels n f.stages.length f.stageCap := by
          apply (fw_active_rectangle_label_mem_iff n f.stages.length f.stageCap _).2
          have hi := (finProdFinEquiv (jj, fwCanonicalChoiceRectangle side) : Fin (5*(4*6))).isLt
          simp only [bridgeDiagonalRectangle, Fin.val_castLE, fwActiveRectangleCount]
          omega
        let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
        have hc := fwBridgeSeedWideGrowthChoice_bridge f.hrect f.hseedrect f.hwide hmax otherChoice jj
          (fwCanonicalChoiceRectangle side)
        refine ⟨hmem, ?_⟩
        cases side <;> simpa [fwCanonicalFamilyLabel, fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
          fwBridgeSeedWideRectangleChoice, fwCanonicalChoiceRectangle, hmax, jj] using hc
    | inr j =>
      have hmem : fwWideRectangle f.hwide (finProdFinEquiv (j, fwCanonicalChoiceRectangle side)) ∈
          fwActiveRectangleLabels n f.stages.length f.stageCap := by
        apply (fw_active_rectangle_label_mem_iff n f.stages.length f.stageCap _).2
        have hi := (finProdFinEquiv (j, fwCanonicalChoiceRectangle side) : Fin ((3*(n/450))*(4*6))).isLt
        simp only [fwWideRectangle, fwActiveRectangleCount]
        omega
      let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
      have hc := fwBridgeSeedWideGrowthChoice_wide f.hrect f.hseedrect f.hwide hmax otherChoice j
        (fwCanonicalChoiceRectangle side)
      refine ⟨hmem, ?_⟩
      cases side <;> simpa [fwCanonicalFamilyLabel, fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice,
        fwBridgeSeedWideRectangleChoice, fwCanonicalChoiceRectangle, hmax] using hc

end
end Sude
