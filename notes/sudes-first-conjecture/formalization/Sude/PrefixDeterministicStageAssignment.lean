import Sude.PrefixStageConditionalAssignment
import Sude.PrefixConstructStateStep

/-! Deterministic stage-preserving simultaneous prefix allocation (DP1–DP3).
Physical square placement and later analytic inputs remain separate. -/
namespace Sude
noncomputable section

/-- For equal-sized labelled value and slot populations in each stage, one
stage-preserving assignment controls all supplied lines simultaneously.
Each stage may have its own mean and numerical interval, with common width
at most `C`; the total line weight of each slot is at most five. -/
theorem prefix_deterministic_stage_assignment {S V G L : Type*}
    [DecidableEq S] [DecidableEq V] [DecidableEq G] [DecidableEq L]
    (slots : Finset S) (values : Finset V) (lines : Finset L)
    (slotStage : S → G) (valueStage : V → G) (x : V → ℝ) (w : L → S → ℝ)
    (C : ℝ) (Q : ℕ)
    (hC : 0 ≤ C)
    (hcard : ∀ g, (slots.filter (fun s => slotStage s = g)).card =
      (values.filter (fun v => valueStage v = g)).card)
    (hcap : ∀ g, (slots.filter (fun s => slotStage s = g)).card ≤ Q)
    (hw : ∀ l ∈ lines, ∀ s ∈ slots, 0 ≤ w l s)
    (hweight : ∀ s ∈ slots, (∑ l ∈ lines, w l s) ≤ 5)
    (hwidth : ∀ u ∈ values, ∀ v ∈ values,
      valueStage u = valueStage v → x v - x u ≤ C) :
    ∃ e : {s // s ∈ slots} ≃ {v // v ∈ values},
      (∀ s, valueStage (e s).val = slotStage s.val) ∧
      (∀ l ∈ lines,
        |(∑ s : {s // s ∈ slots}, w l s.val * x (e s).val) -
          (∑ g ∈ slots.image slotStage,
            (∑ s ∈ slots.filter (fun s => slotStage s = g), w l s) *
              prefixOriginalStageMean values valueStage x g)| ≤
          (Nat.clog 2 Q : ℝ) * (10 * C)) := by
  classical
  apply prefix_stage_conditional_assignment slots values lines slotStage valueStage x w C Q hcard hcap
  intro k hk st hv
  exact prefix_construct_state_step slots values lines slotStage valueStage x w C Q k st
    hC hw hweight hwidth hv

end
end Sude
