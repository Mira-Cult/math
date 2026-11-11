import Sude.FWSelectedThetaWitness
import Sude.FWSeedTraceGridExact
import Sude.FWActiveRectangleLabels
import Mathlib.Data.List.NodupEquivFin

/-! Canonical choice representatives for actual seed and growth stages.
This is label geometry only: it makes no grid, gap, or radius assertion. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- A trace stage occurring in the tagged seed/trace support occurs in the list. -/
theorem fw_seed_trace_stage_mem (stages : List BTSelectedStage) (s : BTSelectedStage)
    (h : Sum.inr s ∈ fwSeedTraceLabels stages) : s ∈ stages := by
  classical
  simpa [fwSeedTraceLabels, fwSeedTraceBase] using h

/-- The two canonical representatives use the first rectangle on each side. -/
def fwCanonicalChoiceRectangle (side : Bool) : Fin (4*6) :=
  if side then 0 else 12

/-- A selected seed or trace stage names one actual rectangle in the desired
choice fiber. The stage index comes from the no-duplicates trace equivalence. -/
def fwCanonicalSeedGrowthLabel {n : ℕ} {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (side : Bool) (x : {x // x ∈ fwSeedTraceLabels f.stages}) : Fin (fwJointRectangleCount n 254) := by
  classical
  rcases x with ⟨x,hx⟩
  cases x with
  | inl j => exact fwSeedRectangle f.hseedrect (finProdFinEquiv (j, fwCanonicalChoiceRectangle side))
  | inr s =>
    let e := List.Nodup.getEquiv f.stages (f.trace.nodup (by omega))
    let j := e.symm ⟨s, fw_seed_trace_stage_mem f.stages s hx⟩
    exact btGrowingOffsetRectangle (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff
      (finProdFinEquiv (j, fwCanonicalChoiceRectangle side))

/-- The abstract seed stage maps to its actual chosen seed rectangle. -/
theorem fw_canonical_seed_label {n : ℕ} {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (j : Fin 16) (hj : Sum.inl j ∈ fwSeedTraceLabels f.stages) :
    fwCanonicalSeedGrowthLabel f side ⟨Sum.inl j, hj⟩ =
      fwSeedRectangle f.hseedrect (finProdFinEquiv (j, fwCanonicalChoiceRectangle side)) := by
  rfl

/-- A trace stage maps to the actual growth rectangle at the unique stage index. -/
theorem fw_canonical_growth_label {n : ℕ} {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (j : Fin f.stages.length)
    (hj : Sum.inr (f.stages.get j) ∈ fwSeedTraceLabels f.stages) :
    fwCanonicalSeedGrowthLabel f side ⟨Sum.inr (f.stages.get j), hj⟩ =
      btGrowingOffsetRectangle (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff
        (finProdFinEquiv (j, fwCanonicalChoiceRectangle side)) := by
  classical
  dsimp [fwCanonicalSeedGrowthLabel]
  simp [List.Nodup.getEquiv, f.trace.nodup (by omega)]

theorem fw_canonical_seed_growth_label_injective {n : ℕ} {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool) :
    Function.Injective (fwCanonicalSeedGrowthLabel f side) := by
  classical
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  apply Subtype.ext
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change fwSeedRectangle f.hseedrect (finProdFinEquiv (a, fwCanonicalChoiceRectangle side)) =
        fwSeedRectangle f.hseedrect (finProdFinEquiv (b, fwCanonicalChoiceRectangle side)) at h
      have hp := finProdFinEquiv.injective (fwSeedRectangle_injective f.hseedrect h)
      exact congrArg Sum.inl (congrArg Prod.fst hp)
    | inr b =>
      exfalso
      dsimp only [fwCanonicalSeedGrowthLabel] at h
      have hv := congrArg Fin.val h
      simp only [fwSeedRectangle, btGrowingOffsetRectangle] at hv
      have ht := (finProdFinEquiv (a, fwCanonicalChoiceRectangle side) : Fin (16 * (4*6))).isLt
      omega
  | inr a =>
    cases b with
    | inl b =>
      exfalso
      dsimp only [fwCanonicalSeedGrowthLabel] at h
      have hv := congrArg Fin.val h
      simp only [fwSeedRectangle, btGrowingOffsetRectangle] at hv
      have ht := (finProdFinEquiv (b, fwCanonicalChoiceRectangle side) : Fin (16 * (4*6))).isLt
      omega
    | inr b =>
      dsimp only [fwCanonicalSeedGrowthLabel] at h
      have hp := finProdFinEquiv.injective (btGrowingOffsetRectangle_injective _ f.hoff h)
      have hi := congrArg Prod.fst hp
      let e := List.Nodup.getEquiv f.stages (f.trace.nodup (by omega))
      have hs : e.symm ⟨a, fw_seed_trace_stage_mem f.stages a ha⟩ =
          e.symm ⟨b, fw_seed_trace_stage_mem f.stages b hb⟩ := hi
      exact congrArg Sum.inr (congrArg Subtype.val (e.symm.injective hs))


/-- Every representative lies in the active rectangle interval. -/
theorem fw_canonical_seed_growth_label_mem {n : ℕ} {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (x : {x // x ∈ fwSeedTraceLabels f.stages}) :
    fwCanonicalSeedGrowthLabel f side x ∈ fwActiveRectangleLabels n f.stages.length f.stageCap := by
  classical
  apply (fw_active_rectangle_label_mem_iff n f.stages.length f.stageCap _).2
  rcases x with ⟨x,hx⟩
  cases x with
  | inl j =>
    change 5*(4*6) + (finProdFinEquiv (j, fwCanonicalChoiceRectangle side) : Fin (16*(4*6))).val < _
    have hj := (finProdFinEquiv (j, fwCanonicalChoiceRectangle side) : Fin (16*(4*6))).isLt
    dsimp [fwActiveRectangleCount]
    omega
  | inr s =>
    dsimp only [fwCanonicalSeedGrowthLabel, btGrowingOffsetRectangle]
    have hj := (finProdFinEquiv ((List.Nodup.getEquiv f.stages (f.trace.nodup (by omega))).symm
      ⟨s, fw_seed_trace_stage_mem f.stages s hx⟩, fwCanonicalChoiceRectangle side) : Fin (f.stages.length*(4*6))).isLt
    dsimp [fwActiveRectangleCount]
    omega

/-- The first and thirteenth rectangle of each realized stage have the
corresponding selected canonical choice, including a shortened trace. -/
theorem fw_canonical_seed_growth_label_choice {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254)
      (fwSelectedThetaChoice hnlo otherChoice)) (side : Bool)
    (x : {x // x ∈ fwSeedTraceLabels f.stages}) :
    fwSelectedThetaChoice hnlo otherChoice (fwCanonicalSeedGrowthLabel f side x) = side := by
  classical
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  rcases x with ⟨x,hx⟩
  cases x with
  | inl j =>
    have hc := fwBridgeSeedWideGrowthChoice_seed f.hrect f.hseedrect f.hwide hmax otherChoice j
      (fwCanonicalChoiceRectangle side)
    cases side <;> simpa [fwSelectedThetaChoice, fwBridgeSeedWideGrowthChoice, fwBridgeSeedWideRectangleChoice,
      fwCanonicalSeedGrowthLabel, fwCanonicalChoiceRectangle, hmax] using hc
  | inr s =>
    let e := List.Nodup.getEquiv f.stages (f.trace.nodup (by omega))
    let j := e.symm ⟨s, fw_seed_trace_stage_mem f.stages s hx⟩
    have hc := fwBridgeSeedWideGrowthChoice_offset_restrict f.hrect f.hseedrect f.hwide hmax
      f.hoff f.stageCap otherChoice j (fwCanonicalChoiceRectangle side)
    cases side <;> simpa [fwCanonicalSeedGrowthLabel, fwSelectedThetaChoice,
      fwBridgeSeedWideGrowthChoice, fwBridgeSeedWideRectangleChoice, fwCanonicalChoiceRectangle, hmax, j, e] using hc

end
end Sude
