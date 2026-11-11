import Sude.BTStageIteration
import Sude.PrimeIndex
import Mathlib.Data.Finset.Sort

/-! Index the actual traced pairs as globally distinct prescribed-pool values. -/
namespace Sude
noncomputable section

/-- Read a stage by its index after proving the exact stage count. -/
def BTStageTrace.stageAt (stages : List BTSelectedStage) {P : ℕ} (hlen : stages.length = P)
    (j : Fin P) : BTSelectedStage := stages.get (Fin.cast hlen.symm j)

theorem BTStageTrace.stageAt_mem (stages : List BTSelectedStage) {P : ℕ} (hlen : stages.length = P)
    (j : Fin P) : BTStageTrace.stageAt stages hlen j ∈ stages := List.get_mem _ _

/-- The lower endpoint in increasing order within an actual traced stage. -/
def BTStageTrace.lowAt {g Q : ℕ} {initial final : Finset ℕ} {R last : ℝ}
    {stages : List BTSelectedStage} (trace : BTStageTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) (j : Fin P) (i : Fin Q) : ℕ :=
  let stage := BTStageTrace.stageAt stages hlen j
  stage.lows.orderEmbOfFin (trace.stage_properties stage (BTStageTrace.stageAt_mem stages hlen j)).2.2.2.1 i

theorem BTStageTrace.lowAt_mem {g Q : ℕ} {initial final : Finset ℕ} {R last : ℝ}
    {stages : List BTSelectedStage} (trace : BTStageTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) (j : Fin P) (i : Fin Q) :
    trace.lowAt hlen j i ∈ (BTStageTrace.stageAt stages hlen j).lows := by
  exact Finset.orderEmbOfFin_mem _ _ _

/-- Both endpoints of a traced stage are actual values from the original
unused stock, including the case of coinciding gap values across stages. -/
theorem BTStageTrace.endpoint_mem_initial {g Q : ℕ} {initial final : Finset ℕ} {R last : ℝ}
    {stages : List BTSelectedStage} (trace : BTStageTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) (j : Fin P) (i : Fin Q) (side : Bool) :
    (if side then trace.lowAt hlen j i + (BTStageTrace.stageAt stages hlen j).gap
      else trace.lowAt hlen j i) ∈ initial := by
  have hm := trace.lowAt_mem hlen j i
  have hs := trace.footprints_subset _ (BTStageTrace.stageAt_mem stages hlen j)
  apply hs
  cases side
  · exact Finset.mem_union_left _ hm
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hm, rfl⟩)

/-- The exact prescribed-pool value at each stage, matching index and side. -/
def BTStageTrace.poolValues {g Q n : ℕ} {initial final : Finset ℕ} {R last : ℝ}
    {stages : List BTSelectedStage} (trace : BTStageTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n) :
    (Fin P × Fin Q) × Bool → pool n := fun x =>
  ⟨if x.2 then trace.lowAt hlen x.1.1 x.1.2 + (BTStageTrace.stageAt stages hlen x.1.1).gap
    else trace.lowAt hlen x.1.1 x.1.2,
    hpool _ (trace.endpoint_mem_initial hlen x.1.1 x.1.2 x.2)⟩

theorem BTStageTrace.poolValues_gap {g Q n : ℕ} {initial final : Finset ℕ} {R last : ℝ}
    {stages : List BTSelectedStage} (trace : BTStageTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (j : Fin P) (i : Fin Q) :
    (trace.poolValues hlen hpool ((j, i), true)).val =
      (trace.poolValues hlen hpool ((j, i), false)).val + (BTStageTrace.stageAt stages hlen j).gap := by
  rfl

/-- Distinct stage indices have disjoint actual endpoint footprints. -/
theorem BTStageTrace.stageAt_disjoint {g Q : ℕ} {initial final : Finset ℕ} {R last : ℝ}
    {stages : List BTSelectedStage} (trace : BTStageTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) {j k : Fin P} (hjk : j ≠ k) :
    Disjoint (BTStageTrace.stageAt stages hlen j).footprint (BTStageTrace.stageAt stages hlen k).footprint := by
  have hp := List.pairwise_iff_get.mp trace.pairwise_disjoint
  rcases lt_or_gt_of_ne hjk with hj | hk
  · have hj' : Fin.cast hlen.symm j < Fin.cast hlen.symm k := by simpa using hj
    exact hp _ _ hj'
  · have hk' : Fin.cast hlen.symm k < Fin.cast hlen.symm j := by simpa using hk
    exact (hp _ _ hk').symm

/-- All indexed stage endpoints are distinct as values of the actual
prescribed pool, both within a stage and across different stages. -/
theorem BTStageTrace.poolValues_injective {g Q n : ℕ} {initial final : Finset ℕ} {R last : ℝ}
    {stages : List BTSelectedStage} (trace : BTStageTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n) :
    Function.Injective (trace.poolValues hlen hpool) := by
  rintro ⟨⟨j, i⟩, s⟩ ⟨⟨k, t⟩, u⟩ heq
  have hv := congrArg Subtype.val heq
  let endpoint := fun (j : Fin P) (i : Fin Q) (s : Bool) =>
    if s then trace.lowAt hlen j i + (BTStageTrace.stageAt stages hlen j).gap else trace.lowAt hlen j i
  have hv' : endpoint j i s = endpoint k t u := hv
  have hmem (j : Fin P) (i : Fin Q) (s : Bool) :
      endpoint j i s ∈ (BTStageTrace.stageAt stages hlen j).footprint := by
    have hm := trace.lowAt_mem hlen j i
    cases s
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hm, rfl⟩)
  by_cases hjk : j = k
  · subst k
    let stage := BTStageTrace.stageAt stages hlen j
    let p := trace.lowAt hlen j i
    let q := trace.lowAt hlen j t
    have hp : p ∈ stage.lows := trace.lowAt_mem hlen j i
    have hq : q ∈ stage.lows := trace.lowAt_mem hlen j t
    have hprops := trace.stage_properties stage (BTStageTrace.stageAt_mem stages hlen j)
    have hpq : p = q := by
      by_contra hne
      have hd := hprops.2.2.2.2 p hp q hq hne
      have hx : endpoint j i s ∈ ({p, p + stage.gap} : Finset ℕ) := by
        cases s <;> simp [endpoint, p, stage]
      have hy : endpoint j t u ∈ ({q, q + stage.gap} : Finset ℕ) := by
        cases u <;> simp [endpoint, q, stage]
      rw [← hv'] at hy
      exact Finset.disjoint_left.mp hd hx hy
    have hi : i = t := by
      apply (stage.lows.orderEmbOfFin hprops.2.2.2.1).injective
      exact hpq
    subst t
    have hs : s = u := by
      have hgap := hprops.1
      cases s <;> cases u <;> simp_all [endpoint, p, stage]
    subst u
    rfl
  · have hd := trace.stageAt_disjoint hlen hjk
    have hx := hmem j i s
    have hy := hmem k t u
    rw [← hv'] at hy
    exact False.elim (Finset.disjoint_left.mp hd hx hy)

end
end Sude
