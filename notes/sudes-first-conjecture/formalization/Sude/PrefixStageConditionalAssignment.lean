import Sude.PrefixConditionalRecursiveAssignment
import Sude.PrefixInitialSplitState

/-! A stage-preserving conditional DP3 assignment from an actual initial
stage partition. The common one-step existence theorem is still supplied. -/
namespace Sude
noncomputable section

/-- The mean of values in a stage, with totalized empty-stage division. -/
def prefixOriginalStageMean {V G : Type*} [DecidableEq G]
    (values : Finset V) (valueStage : V → G) (x : V → ℝ) (g : G) : ℝ :=
  (∑ v ∈ values.filter (fun v => valueStage v = g), x v) /
    ((values.filter (fun v => valueStage v = g)).card : ℝ)

/-- A weighted stage-mean sum is the same whether grouped by stage or by
slot. This uses all slots, including zero-weight slots. -/
theorem prefix_stage_mean_grouping {S V G L : Type*} [DecidableEq G]
    (slots : Finset S) (values : Finset V) (slotStage : S → G) (valueStage : V → G)
    (x : V → ℝ) (w : L → S → ℝ) (l : L) :
    (∑ s ∈ slots, w l s * prefixOriginalStageMean values valueStage x (slotStage s)) =
      ∑ g ∈ slots.image slotStage,
        (∑ s ∈ slots.filter (fun s => slotStage s = g), w l s) *
          prefixOriginalStageMean values valueStage x g := by
  classical
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := slots) (t := slots.image slotStage) (g := slotStage)
    (fun s hs => Finset.mem_image_of_mem slotStage hs)
    (fun s => w l s * prefixOriginalStageMean values valueStage x (slotStage s))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro g hg
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have hsg := (Finset.mem_filter.mp hs).2
  rw [hsg]

/-- The stage partition gives the initial state and exact grouped baseline;
a supplied common valid split-step theorem then yields one stage-preserving
bijection with a global bound on every line. -/
theorem prefix_stage_conditional_assignment {S V G L : Type*}
    [DecidableEq S] [DecidableEq V] [DecidableEq G] [DecidableEq L]
    (slots : Finset S) (values : Finset V) (lines : Finset L)
    (slotStage : S → G) (valueStage : V → G) (x : V → ℝ) (w : L → S → ℝ)
    (C : ℝ) (Q : ℕ)
    (hcard : ∀ g, (slots.filter (fun s => slotStage s = g)).card =
      (values.filter (fun v => valueStage v = g)).card)
    (hcap : ∀ g, (slots.filter (fun s => slotStage s = g)).card ≤ Q)
    (hstep : ∀ k < Nat.clog 2 Q, ∀ st,
      PrefixSplitStateValid slots values slotStage valueStage Q k st →
      ∃ next, PrefixSplitStateValid slots values slotStage valueStage Q (k + 1) next ∧
        PrefixSplitStateStep slots values lines x w C st next) :
    ∃ e : {s // s ∈ slots} ≃ {v // v ∈ values},
      (∀ s, valueStage (e s).val = slotStage s.val) ∧
      (∀ l ∈ lines,
        |(∑ s : {s // s ∈ slots}, w l s.val * x (e s).val) -
          (∑ g ∈ slots.image slotStage,
            (∑ s ∈ slots.filter (fun s => slotStage s = g), w l s) *
              prefixOriginalStageMean values valueStage x g)| ≤
          (Nat.clog 2 Q : ℝ) * (10 * C)) := by
  classical
  apply prefix_conditional_recursive_assignment_clog slots values lines slotStage valueStage x w
    (fun l => ∑ g ∈ slots.image slotStage,
      (∑ s ∈ slots.filter (fun s => slotStage s = g), w l s) *
        prefixOriginalStageMean values valueStage x g)
    C Q (prefixInitialSplitState slotStage valueStage)
    (prefix_initial_split_state_valid slots values slotStage valueStage Q hcard hcap) ?_ hstep
  intro l hl
  rw [prefix_initial_split_state_line_mean]
  exact prefix_stage_mean_grouping slots values slotStage valueStage x w l

end
end Sude
