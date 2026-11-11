import Sude.BTStageTrace
import Sude.StepGrid

/-! The variable-gap trace extends an actual complete step grid. -/
namespace Sude
noncomputable section

local instance : DecidableEq BTSelectedStage := Classical.decEq _

/-- Positive pair populations and cross-stage disjointness imply that the
stage records themselves are distinct. -/
theorem BTStageTrace.nodup {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℝ} {stages : List BTSelectedStage}
    (trace : BTStageTrace g Q unused radius final last stages) (hQ : 0 < Q) : stages.Nodup := by
  induction trace with
  | nil => simp
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      have hp : 0 < stage.lows.card := by omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hp
      have hfoot : p ∈ stage.footprint := Finset.mem_union_left _ hp
      have htail := hrest.footprints_subset stage hmem
      exact (Finset.mem_sdiff.mp (htail hfoot)).2 hfoot
    · exact ih

/-- Each traced gap joins the already accumulated step grid: the next
selected gap never exceeds the previous real radius, while the accumulated
grid radius only grows. -/
theorem BTStageTrace.step_gap_chain {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℝ} {stages : List BTSelectedStage}
    (trace : BTStageTrace g Q unused radius final last stages) (gridRadius : ℕ)
    (hstart : radius ≤ gridRadius) :
    StepGapChain BTSelectedStage.gap g gridRadius stages := by
  induction trace generalizing gridRadius with
  | nil => exact StepGapChain.nil _
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    have hleR : (stage.gap : ℝ) ≤ gridRadius := hbound.trans hstart
    have hle : stage.gap ≤ gridRadius := by exact_mod_cast hleR
    apply StepGapChain.cons gridRadius stage tail hdiv (by omega)
    apply ih
    exact_mod_cast (show stage.gap ≤ gridRadius + stage.gap by omega)

/-- A traced sequence extends a supplied complete `g`-grid to the exact sum
of the initial radius and all selected stage gaps. -/
theorem BTStageTrace.extend_step_grid {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℝ} {stages : List BTSelectedStage}
    (trace : BTStageTrace g Q unused radius final last stages)
    (base : Finset BTSelectedStage) (gridRadius : ℕ) (hg : 0 < g) (hQ : 0 < Q)
    (hbase : CompleteStepGrid base BTSelectedStage.gap g gridRadius)
    (hdiv : g ∣ gridRadius) (hstart : radius ≤ gridRadius)
    (hfresh : ∀ stage ∈ stages, stage ∉ base) :
    CompleteStepGrid (base ∪ stages.toFinset) BTSelectedStage.gap g
      (gridRadius + (stages.map BTSelectedStage.gap).sum) :=
  extend_step_gap_chain BTSelectedStage.gap g base gridRadius stages hg hbase hdiv
    (trace.nodup hQ) hfresh (trace.step_gap_chain gridRadius hstart)

/-- An abstract initial label of gap `g`. A later physical realization must
supply its own distinct seed pair with that gap. -/
def btSeedLabel (g : ℕ) : BTSelectedStage := ⟨g, ∅, 0⟩

/-- One abstract seed of gap `g` realizes both multiples through `g`. -/
theorem bt_seed_step_grid (g : ℕ) (hg : 0 < g) :
    CompleteStepGrid {btSeedLabel g} BTSelectedStage.gap g g := by
  intro t ht hd
  obtain ⟨j, hj⟩ := hd
  have hjle : j ≤ 1 := by
    by_contra hn
    have hj2 : 2 ≤ j := by omega
    have hm := Nat.mul_le_mul_left g hj2
    nlinarith [hm]
  have hjcases : j = 0 ∨ j = 1 := by omega
  rcases hjcases with hj0 | hj1
  · subst j
    simp at hj
    subst t
    exact ⟨∅, by simp, by simp⟩
  · subst j
    simp at hj
    subst t
    exact ⟨{btSeedLabel g}, by simp, by simp [btSeedLabel]⟩

/-- With an initial seed radius `g`, the actual traced gaps form a complete
`g`-step grid through their full accumulated sum. The seed label is abstract
and has not yet been assigned a physical pair. -/
theorem BTStageTrace.seeded_step_grid {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℝ} {stages : List BTSelectedStage}
    (trace : BTStageTrace g Q unused radius final last stages)
    (hg : 0 < g) (hQ : 0 < Q) (hstart : radius ≤ g) :
    CompleteStepGrid ({btSeedLabel g} ∪ stages.toFinset) BTSelectedStage.gap g
      (g + (stages.map BTSelectedStage.gap).sum) := by
  apply trace.extend_step_grid {btSeedLabel g} g hg hQ (bt_seed_step_grid g hg) (dvd_refl g) hstart
  intro stage hs
  have hp := trace.stage_properties stage hs
  intro he
  have heq : stage = btSeedLabel g := by simpa using he
  have hc := congrArg (fun z : BTSelectedStage => z.lows.card) heq
  simp [btSeedLabel] at hc
  have hcard := hp.2.2.2.1
  rw [hc] at hcard
  simp at hcard
  omega

end
end Sude
