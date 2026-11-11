import Sude.BTSourceGate

/-! Exact repeated-stage bookkeeping on actual unused prime values. -/
namespace Sude
noncomputable section

/-- A retained common-gap matching for one stage. -/
structure BTSelectedStage where
  gap : ℕ
  lows : Finset ℕ
  minimum : ℝ

def BTSelectedStage.footprint (s : BTSelectedStage) : Finset ℕ := pairFootprint s.lows s.gap

/-- Each stage removes its actual pair footprint before the next stage and
uses its chosen gap as the next real radius. -/
inductive BTStageTrace (g Q : ℕ) : Finset ℕ → ℝ → Finset ℕ → ℝ → List BTSelectedStage → Prop
  | nil (unused : Finset ℕ) (radius : ℝ) : BTStageTrace g Q unused radius unused radius []
  | cons (unused : Finset ℕ) (radius : ℝ) (stage : BTSelectedStage)
      (final : Finset ℕ) (lastRadius : ℝ) (tail : List BTSelectedStage)
      (hgap : 0 < stage.gap) (hdiv : g ∣ stage.gap)
      (hbound : (stage.gap : ℝ) ≤ radius) (hminimum : stage.minimum ≤ stage.gap)
      (hcard : stage.lows.card = Q) (hmatch : PairwiseDisjointPairs stage.lows stage.gap)
      (hsub : stage.footprint ⊆ unused)
      (hrest : BTStageTrace g Q (unused \ stage.footprint) stage.gap final lastRadius tail) :
      BTStageTrace g Q unused radius final lastRadius (stage :: tail)

/-- Every later endpoint remains in the initial unused set. -/
theorem BTStageTrace.footprints_subset {g Q : ℕ} {unused final : Finset ℕ}
    {radius lastRadius : ℝ} {stages : List BTSelectedStage}
    (h : BTStageTrace g Q unused radius final lastRadius stages) :
    ∀ stage ∈ stages, stage.footprint ⊆ unused := by
  induction h with
  | nil => simp
  | cons unused radius stage final lastRadius tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hsub
    · exact (ih s hs).trans Finset.sdiff_subset

/-- Every recorded stage retains its selected lower-gap bound and its
exact matching size. -/
theorem BTStageTrace.stage_properties {g Q : ℕ} {unused final : Finset ℕ}
    {radius lastRadius : ℝ} {stages : List BTSelectedStage}
    (h : BTStageTrace g Q unused radius final lastRadius stages) :
    ∀ stage ∈ stages, 0 < stage.gap ∧ g ∣ stage.gap ∧ stage.minimum ≤ stage.gap ∧
      stage.lows.card = Q ∧ PairwiseDisjointPairs stage.lows stage.gap := by
  induction h with
  | nil => simp
  | cons unused radius stage final lastRadius tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨hgap, hdiv, hminimum, hcard, hmatch⟩
    · exact ih s hs

/-- Stages never reuse an endpoint, even when their gap values coincide. -/
theorem BTStageTrace.pairwise_disjoint {g Q : ℕ} {unused final : Finset ℕ}
    {radius lastRadius : ℝ} {stages : List BTSelectedStage}
    (h : BTStageTrace g Q unused radius final lastRadius stages) :
    stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons unused radius stage final lastRadius tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    apply List.Pairwise.cons
    · intro s hs
      have htail := hrest.footprints_subset s hs
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact (Finset.mem_sdiff.mp (htail hz')).2 hz
    · exact ih

/-- The final unused set is a subset of the initial one, with exactly two
entries removed for each selected pair at every stage. -/
theorem BTStageTrace.final_subset_and_card {g Q : ℕ} {unused final : Finset ℕ}
    {radius lastRadius : ℝ} {stages : List BTSelectedStage}
    (h : BTStageTrace g Q unused radius final lastRadius stages) :
    final ⊆ unused ∧ final.card + 2 * Q * stages.length = unused.card := by
  induction h with
  | nil => simp
  | cons unused radius stage final lastRadius tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    have hfoot : stage.footprint.card = 2 * Q := by
      rw [BTSelectedStage.footprint, pairFootprint_card stage.lows stage.gap hgap hmatch, hcard]
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    rw [hfoot] at hc
    refine ⟨ih.1.trans Finset.sdiff_subset, ?_⟩
    simp only [List.length_cons, Nat.mul_succ]
    omega

end
end Sude
