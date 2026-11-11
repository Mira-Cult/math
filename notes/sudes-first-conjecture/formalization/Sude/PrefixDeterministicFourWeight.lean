import Sude.PrefixDeterministicStageAssignment

/-! The four-incidence corollary of deterministic stage allocation. This
is abstract and does not assert any physical-square incidence hypothesis. -/
namespace Sude
noncomputable section

/-- If each slot has total line weight at most four, simultaneous allocation
has discrepancy at most `8*C` per balanced depth. This is obtained by scaling
all weights together; the same assignment is used for every supplied line. -/
theorem prefix_deterministic_stage_assignment_four {S V G L : Type*}
    [DecidableEq S] [DecidableEq V] [DecidableEq G] [DecidableEq L]
    (slots : Finset S) (values : Finset V) (lines : Finset L)
    (slotStage : S → G) (valueStage : V → G) (x : V → ℝ) (w : L → S → ℝ)
    (C : ℝ) (Q : ℕ)
    (hC : 0 ≤ C)
    (hcard : ∀ g, (slots.filter (fun s => slotStage s = g)).card =
      (values.filter (fun v => valueStage v = g)).card)
    (hcap : ∀ g, (slots.filter (fun s => slotStage s = g)).card ≤ Q)
    (hw : ∀ l ∈ lines, ∀ s ∈ slots, 0 ≤ w l s)
    (hweight : ∀ s ∈ slots, (∑ l ∈ lines, w l s) ≤ 4)
    (hwidth : ∀ u ∈ values, ∀ v ∈ values,
      valueStage u = valueStage v → x v - x u ≤ C) :
    ∃ e : {s // s ∈ slots} ≃ {v // v ∈ values},
      (∀ s, valueStage (e s).val = slotStage s.val) ∧
      (∀ l ∈ lines,
        |(∑ s : {s // s ∈ slots}, w l s.val * x (e s).val) -
          (∑ g ∈ slots.image slotStage,
            (∑ s ∈ slots.filter (fun s => slotStage s = g), w l s) *
              prefixOriginalStageMean values valueStage x g)| ≤
          (Nat.clog 2 Q : ℝ) * (8 * C)) := by
  classical
  let k : ℝ := 5 / 4
  have hk : 0 < k := by dsimp [k]; norm_num
  have hw' : ∀ l ∈ lines, ∀ s ∈ slots, 0 ≤ k * w l s := by
    intro l hl s hs
    exact mul_nonneg (le_of_lt hk) (hw l hl s hs)
  have hweight' : ∀ s ∈ slots, (∑ l ∈ lines, k * w l s) ≤ 5 := by
    intro s hs
    rw [← Finset.mul_sum]
    have hh := hweight s hs
    dsimp [k]
    nlinarith
  obtain ⟨e, he, hb⟩ := prefix_deterministic_stage_assignment slots values lines
    slotStage valueStage x (fun l s => k * w l s) C Q hC hcard hcap hw' hweight' hwidth
  refine ⟨e, he, ?_⟩
  intro l hl
  have hleft : (∑ s : {s // s ∈ slots}, (k * w l s.val) * x (e s).val) =
      k * (∑ s : {s // s ∈ slots}, w l s.val * x (e s).val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hright : (∑ g ∈ slots.image slotStage,
      (∑ s ∈ slots.filter (fun s => slotStage s = g), k * w l s) *
        prefixOriginalStageMean values valueStage x g) =
      k * (∑ g ∈ slots.image slotStage,
        (∑ s ∈ slots.filter (fun s => slotStage s = g), w l s) *
          prefixOriginalStageMean values valueStage x g) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [← Finset.mul_sum]
    ring
  have hh := hb l hl
  rw [hleft, hright, ← mul_sub, abs_mul, abs_of_pos hk] at hh
  dsimp [k] at hh
  change |(∑ s ∈ slots.attach, w l s.val * x (e s).val) -
      (∑ g ∈ slots.image slotStage,
        (∑ s ∈ slots.filter (fun s => slotStage s = g), w l s) *
          prefixOriginalStageMean values valueStage x g)| ≤
        (Nat.clog 2 Q : ℝ) * (8 * C)
  nlinarith

end
end Sude
