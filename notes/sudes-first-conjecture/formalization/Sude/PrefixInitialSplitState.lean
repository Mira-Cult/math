import Sude.PrefixSplitStateSequence

/-! Initial stage-key state and baseline conditional means for DP3. This does
not construct subsequent split states or a final allocation. -/
namespace Sude
noncomputable section

/-- Initially each slot and value retains its original stage and empty split
history. -/
def prefixInitialSplitState {S V G : Type*} (slotStage : S → G) (valueStage : V → G) :
    PrefixSplitKeyState S V G where
  slotKey s := (slotStage s, [])
  valueKey v := (valueStage v, [])

/-- Matching stage-fiber cardinalities and a stage capacity establish the
initial invariant, including keys with nonempty histories. -/
theorem prefix_initial_split_state_valid {S V G : Type*} [DecidableEq G]
    (slots : Finset S) (values : Finset V) (slotStage : S → G) (valueStage : V → G)
    (Q : ℕ)
    (hcard : ∀ g, (slots.filter (fun s => slotStage s = g)).card =
      (values.filter (fun v => valueStage v = g)).card)
    (hcap : ∀ g, (slots.filter (fun s => slotStage s = g)).card ≤ Q) :
    PrefixSplitStateValid slots values slotStage valueStage Q 0
      (prefixInitialSplitState slotStage valueStage) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs; rfl
  · intro v hv; rfl
  · rintro ⟨g,h⟩
    cases h with
    | nil => simpa [prefixInitialSplitState] using hcard g
    | cons b t => simp [prefixInitialSplitState]
  · rintro ⟨g,h⟩
    cases h with
    | nil => simpa [prefixInitialSplitState, prefixBalancedMax] using hcap g
    | cons b t => simp [prefixInitialSplitState, prefixBalancedMax]

/-- The initial conditional-mean line total is exactly the weighted sum of
original stage means. Numerical values may repeat as labels remain distinct. -/
theorem prefix_initial_split_state_line_mean {S V G L : Type*} [DecidableEq G]
    (slots : Finset S) (values : Finset V) (slotStage : S → G) (valueStage : V → G)
    (x : V → ℝ) (w : L → S → ℝ) (l : L) :
    prefixSplitStateLineMean slots values x w (prefixInitialSplitState slotStage valueStage) l =
      ∑ s ∈ slots, w l s *
        ((∑ v ∈ values.filter (fun v => valueStage v = slotStage s), x v) /
          ((values.filter (fun v => valueStage v = slotStage s)).card : ℝ)) := by
  classical
  simp [prefixSplitStateLineMean, prefixInitialSplitState]

end
end Sude
