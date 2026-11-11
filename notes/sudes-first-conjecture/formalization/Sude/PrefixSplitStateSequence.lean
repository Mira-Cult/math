import Sude.PrefixBalancedSplitDepth

/-! A finite common sequence of simultaneous split states. This is conditional
on a one-step existence hypothesis and does not construct the splits. -/
namespace Sude
noncomputable section

/-- Slot and labelled-value keys share the original stage and a finite history
of split choices. -/
structure PrefixSplitKeyState (S V G : Type*) where
  slotKey : S → G × List Bool
  valueKey : V → G × List Bool

/-- The line's conditional-mean total for a single state. Empty fibers use
Lean's totalized division, but matching counts ensure actual slot fibers have
nonempty corresponding value fibers. -/
def prefixSplitStateLineMean {S V G L : Type*} [DecidableEq G]
    (slots : Finset S) (values : Finset V) (x : V → ℝ) (w : L → S → ℝ)
    (st : PrefixSplitKeyState S V G) (l : L) : ℝ :=
  ∑ s ∈ slots, w l s *
    ((∑ v ∈ values.filter (fun v => st.valueKey v = st.slotKey s), x v) /
      ((values.filter (fun v => st.valueKey v = st.slotKey s)).card : ℝ))

/-- A valid state retains stages, matches each key's slot and value counts,
and obeys the supplied balanced group-size bound. -/
def PrefixSplitStateValid {S V G : Type*} [DecidableEq G]
    (slots : Finset S) (values : Finset V) (slotStage : S → G) (valueStage : V → G)
    (Q k : ℕ) (st : PrefixSplitKeyState S V G) : Prop :=
  (∀ s ∈ slots, (st.slotKey s).1 = slotStage s) ∧
  (∀ v ∈ values, (st.valueKey v).1 = valueStage v) ∧
  (∀ p, (slots.filter (fun s => st.slotKey s = p)).card =
    (values.filter (fun v => st.valueKey v = p)).card) ∧
  (∀ p, (slots.filter (fun s => st.slotKey s = p)).card ≤ prefixBalancedMax Q k)

/-- One shared split refines both keys and bounds the change in each line's
actual conditional-mean total. Its existence is a separate obligation. -/
def PrefixSplitStateStep {S V G L : Type*} [DecidableEq S] [DecidableEq V]
    [DecidableEq G] (slots : Finset S) (values : Finset V) (lines : Finset L)
    (x : V → ℝ) (w : L → S → ℝ) (C : ℝ)
    (old new : PrefixSplitKeyState S V G) : Prop :=
  ∃ chosen : Finset S, ∃ lower : Finset V,
    chosen ⊆ slots ∧ lower ⊆ values ∧
    (∀ s ∈ slots, new.slotKey s = ((old.slotKey s).1,
      (old.slotKey s).2.concat (decide (s ∈ chosen)))) ∧
    (∀ v ∈ values, new.valueKey v = ((old.valueKey v).1,
      (old.valueKey v).2.concat (decide (v ∈ lower)))) ∧
    (∀ l ∈ lines, |prefixSplitStateLineMean slots values x w new l -
      prefixSplitStateLineMean slots values x w old l| ≤ 10 * C)

/-- A supplied property-preserving split theorem can be iterated through `D`
levels to obtain one common state sequence for every line. This lemma neither
proves the one-step hypothesis nor constructs a terminal bijection. -/
theorem prefix_split_state_sequence {S V G L : Type*} [DecidableEq S]
    [DecidableEq V] [DecidableEq G] [DecidableEq L]
    (slots : Finset S) (values : Finset V) (lines : Finset L)
    (slotStage : S → G) (valueStage : V → G) (x : V → ℝ) (w : L → S → ℝ)
    (C : ℝ) (Q D : ℕ) (initial : PrefixSplitKeyState S V G)
    (h0 : PrefixSplitStateValid slots values slotStage valueStage Q 0 initial)
    (hstep : ∀ k < D, ∀ st,
      PrefixSplitStateValid slots values slotStage valueStage Q k st →
      ∃ next, PrefixSplitStateValid slots values slotStage valueStage Q (k + 1) next ∧
        PrefixSplitStateStep slots values lines x w C st next) :
    ∃ sequence : ℕ → PrefixSplitKeyState S V G,
      sequence 0 = initial ∧
      (∀ k ≤ D, PrefixSplitStateValid slots values slotStage valueStage Q k (sequence k)) ∧
      (∀ k < D, PrefixSplitStateStep slots values lines x w C (sequence k) (sequence (k + 1))) := by
  classical
  let next : ℕ → PrefixSplitKeyState S V G → PrefixSplitKeyState S V G :=
    fun k st => if h : k < D ∧ PrefixSplitStateValid slots values slotStage valueStage Q k st then
      Classical.choose (hstep k h.1 st h.2) else st
  let sequence : ℕ → PrefixSplitKeyState S V G := Nat.rec initial (fun k st => next k st)
  have hn : ∀ k < D, ∀ st,
      PrefixSplitStateValid slots values slotStage valueStage Q k st →
      PrefixSplitStateValid slots values slotStage valueStage Q (k + 1) (next k st) ∧
        PrefixSplitStateStep slots values lines x w C st (next k st) := by
    intro k hk st hs
    dsimp [next]
    rw [dif_pos ⟨hk, hs⟩]
    exact Classical.choose_spec (hstep k hk st hs)
  have hv : ∀ k ≤ D, PrefixSplitStateValid slots values slotStage valueStage Q k (sequence k) := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk
      have hkd : k < D := by omega
      have hprev := ih (by omega)
      exact (hn k hkd (sequence k) hprev).1
  refine ⟨sequence, rfl, hv, ?_⟩
  intro k hk
  exact (hn k hk (sequence k) (hv k (by omega))).2

end
end Sude
