import Sude.PrefixSplitTerminalAssignment
import Sude.PrefixDepthTelescope

/-! Conditional DP3 composition: a common sequence of valid split states
with one global depth error yields one stage-preserving labelled assignment.
Constructing the one-step split and initial stage baseline is separate. -/
namespace Sude
noncomputable section

/-- Conditional recursive assignment from a supplied common split-step
existence theorem and an initial potential identity. The same chosen sequence
and bijection work simultaneously for all lines. -/
theorem prefix_conditional_recursive_assignment {S V G L : Type*}
    [DecidableEq S] [DecidableEq V] [DecidableEq G] [DecidableEq L]
    (slots : Finset S) (values : Finset V) (lines : Finset L)
    (slotStage : S → G) (valueStage : V → G) (x : V → ℝ) (w : L → S → ℝ)
    (baseline : L → ℝ) (C : ℝ) (Q D : ℕ) (initial : PrefixSplitKeyState S V G)
    (hQ : Q ≤ 2 ^ D)
    (h0 : PrefixSplitStateValid slots values slotStage valueStage Q 0 initial)
    (hbase : ∀ l ∈ lines, prefixSplitStateLineMean slots values x w initial l = baseline l)
    (hstep : ∀ k < D, ∀ st,
      PrefixSplitStateValid slots values slotStage valueStage Q k st →
      ∃ next, PrefixSplitStateValid slots values slotStage valueStage Q (k + 1) next ∧
        PrefixSplitStateStep slots values lines x w C st next) :
    ∃ e : {s // s ∈ slots} ≃ {v // v ∈ values},
      (∀ s, valueStage (e s).val = slotStage s.val) ∧
      (∀ l ∈ lines,
        |(∑ s : {s // s ∈ slots}, w l s.val * x (e s).val) - baseline l| ≤
          (D : ℝ) * (10 * C)) := by
  classical
  obtain ⟨sequence, hstart, hvalid, hsteps⟩ :=
    prefix_split_state_sequence slots values lines slotStage valueStage x w C Q D initial h0 hstep
  obtain ⟨e, hstage, hend⟩ :=
    prefix_split_terminal_assignment slots values slotStage valueStage x w Q D (sequence D)
      (hvalid D le_rfl) hQ
  refine ⟨e, hstage, ?_⟩
  intro l hl
  have hdepth : ∀ i < D,
      |prefixSplitStateLineMean slots values x w (sequence (i + 1)) l -
        prefixSplitStateLineMean slots values x w (sequence i) l| ≤ 10 * C := by
    intro i hi
    obtain ⟨chosen, lower, hcs, hls, hsk, hvk, hline⟩ := hsteps i hi
    exact hline l hl
  have hsum := prefix_depth_telescope (fun i => prefixSplitStateLineMean slots values x w (sequence i) l)
    D (10 * C) hdepth
  rw [hstart, hbase l hl] at hsum
  rw [hend l]
  exact hsum


/-- The same conditional conclusion at the exact base-two ceiling-log depth.
When `Q` is zero or one, this depth is zero. -/
theorem prefix_conditional_recursive_assignment_clog {S V G L : Type*}
    [DecidableEq S] [DecidableEq V] [DecidableEq G] [DecidableEq L]
    (slots : Finset S) (values : Finset V) (lines : Finset L)
    (slotStage : S → G) (valueStage : V → G) (x : V → ℝ) (w : L → S → ℝ)
    (baseline : L → ℝ) (C : ℝ) (Q : ℕ) (initial : PrefixSplitKeyState S V G)
    (h0 : PrefixSplitStateValid slots values slotStage valueStage Q 0 initial)
    (hbase : ∀ l ∈ lines, prefixSplitStateLineMean slots values x w initial l = baseline l)
    (hstep : ∀ k < Nat.clog 2 Q, ∀ st,
      PrefixSplitStateValid slots values slotStage valueStage Q k st →
      ∃ next, PrefixSplitStateValid slots values slotStage valueStage Q (k + 1) next ∧
        PrefixSplitStateStep slots values lines x w C st next) :
    ∃ e : {s // s ∈ slots} ≃ {v // v ∈ values},
      (∀ s, valueStage (e s).val = slotStage s.val) ∧
      (∀ l ∈ lines,
        |(∑ s : {s // s ∈ slots}, w l s.val * x (e s).val) - baseline l| ≤
          (Nat.clog 2 Q : ℝ) * (10 * C)) := by
  apply prefix_conditional_recursive_assignment slots values lines slotStage valueStage x w
    baseline C Q (Nat.clog 2 Q) initial _ h0 hbase hstep
  exact Nat.le_pow_clog (by norm_num) Q

end
end Sude
