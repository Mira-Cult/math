import Sude.PrefixSplitStateSequence
import Sude.PrefixFiberKeyEquivalence
import Sude.PrefixTerminalWeightedSum

/-! Exact terminal transport from a valid split state to one stage-preserving
labelled assignment. Constructing the split states and their discrepancy
bounds remains separate. -/
namespace Sude
noncomputable section

/-- A valid terminal state whose initial group size fits in `2^D` has
singleton final fibers. The resulting one labelled bijection preserves the
original stage and realizes the terminal line potential on every line. -/
theorem prefix_split_terminal_assignment {S V G L : Type*} [DecidableEq S]
    [DecidableEq V] [DecidableEq G]
    (slots : Finset S) (values : Finset V) (slotStage : S → G) (valueStage : V → G)
    (x : V → ℝ) (w : L → S → ℝ) (Q D : ℕ) (st : PrefixSplitKeyState S V G)
    (hvalid : PrefixSplitStateValid slots values slotStage valueStage Q D st)
    (hQ : Q ≤ 2 ^ D) :
    ∃ e : {s // s ∈ slots} ≃ {v // v ∈ values},
      (∀ s, valueStage (e s).val = slotStage s.val) ∧
      (∀ l, (∑ s : {s // s ∈ slots}, w l s.val * x (e s).val) =
        prefixSplitStateLineMean slots values x w st l) := by
  classical
  obtain ⟨hslot, hval, hcard, hbound⟩ := hvalid
  have hsmall : ∀ k, (values.filter (fun v => st.valueKey v = k)).card ≤ 1 := by
    intro k
    calc
      _ = (slots.filter (fun s => st.slotKey s = k)).card := (hcard k).symm
      _ ≤ prefixBalancedMax Q D := hbound k
      _ ≤ 1 := prefix_balanced_max_le_one D Q hQ
  obtain ⟨e, he, hm⟩ := prefix_singleton_key_fiber_value_mean slots values
    st.slotKey st.valueKey x hcard hsmall
  refine ⟨e, ?_, ?_⟩
  · intro s
    calc
      valueStage (e s).val = (st.valueKey (e s).val).1 := (hval (e s).val (e s).property).symm
      _ = (st.slotKey s.val).1 := congrArg Prod.fst (he s)
      _ = slotStage s.val := hslot s.val s.property
  · intro l
    simpa only [prefixSplitStateLineMean] using
      prefix_terminal_weighted_sum slots values st.slotKey w x
        (fun k => (∑ v ∈ values.filter (fun v => st.valueKey v = k), x v) /
          ((values.filter (fun v => st.valueKey v = k)).card : ℝ)) e hm l

end
end Sude
