import Shared.Beeping.ComparisonSingleTape
import Shared.Beeping.Events

/-! Totalize a silent post-Turing evaluator with a finite extra stop state.
The stop state repeatedly writes the symbol already under the head, preserving
the entire tape. It is an adapter for a finite evaluator, not a controller:
a caller still needs a proved dispatch and result-reading protocol. -/
namespace Shared.Beeping.TM0Totalize
open Turing
open Shared.ComplexityBridge.TM2Symbols

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

/-- Halt becomes an explicit transition to `none`; the stop state's rows
write back the scanned symbol. Every row returns a transition. -/
def table (M : TM0.Machine Γ Λ) : TM0.Machine Γ (Option Λ)
  | none, a => some (none, .write a)
  | some q, a => match M q a with
      | none => some (none, .write a)
      | some (q', cmd) => some (some q', cmd)

def embed (c : TM0.Cfg Γ Λ) : TM0.Cfg Γ (Option Λ) := ⟨some c.q, c.Tape⟩
def stopped (T : Tape Γ) : TM0.Cfg Γ (Option Λ) := ⟨none, T⟩

theorem step_live (M : TM0.Machine Γ Λ) (c d : TM0.Cfg Γ Λ)
    (h : TM0.step M c = some d) : TM0.step (table M) (embed c) = some (embed d) := by
  cases c with
  | mk q T =>
    cases hm : M q T.1 with
    | none => simp [TM0.step,hm] at h
    | some p =>
      cases p with
      | mk q' cmd =>
        simp only [TM0.step,hm,Option.map_some,Option.some.injEq] at h
        subst d
        simp [TM0.step, table, embed, hm]

theorem step_terminal (M : TM0.Machine Γ Λ) (c : TM0.Cfg Γ Λ)
    (h : TM0.step M c = none) : TM0.step (table M) (embed c) = some (stopped c.Tape) := by
  cases c with
  | mk q T =>
    cases hm : M q T.1 with
    | none => simp [TM0.step,table,embed,stopped,hm,Tape.write_self]
    | some p => simp [TM0.step,hm] at h

theorem step_stopped (M : TM0.Machine Γ Λ) (T : Tape Γ) :
    TM0.step (table M) (stopped T) = some (stopped T) := by
  simp [TM0.step,table,stopped,Tape.write_self]

theorem step_total (M : TM0.Machine Γ Λ) (c : TM0.Cfg Γ (Option Λ)) :
    ∃ d, TM0.step (table M) c = some d := by
  cases c with
  | mk q T =>
    cases q with
    | none => exact ⟨stopped T, step_stopped M T⟩
    | some q =>
      cases hm : M q T.1 with
      | none => exact ⟨stopped T, by simp [TM0.step,table,stopped,hm,Tape.write_self]⟩
      | some p => cases p with
        | mk q' cmd => exact ⟨⟨some q', match cmd with | .move d => T.move d | .write a => T.write a⟩,
            by cases cmd <;> simp [TM0.step,table,hm]⟩

/-- Exactly one additional stop state is added to the supported state set. -/
def support [DecidableEq Λ] (states : Finset Λ) : Finset (Option Λ) :=
  insert none (states.image some)

theorem support_card [DecidableEq Λ] (states : Finset Λ) :
    (support states).card = states.card + 1 := by
  have h := Finset.card_image_of_injective states (@Option.some.inj Λ)
  simp [support, h]

theorem table_support [DecidableEq Λ] (M : TM0.Machine Γ Λ) (states : Finset Λ)
    (h : TM0.Supports M (states : Set Λ)) :
    TM0.Supports (table M) (support states : Set (Option Λ)) := by
  classical
  constructor
  · change (none : Option Λ) ∈ support states
    simp [support]
  · intro q a q' cmd hstep hq
    cases q with
    | none =>
      simp [table] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      simp [support]
    | some q =>
      have hq' : q ∈ states := by simpa [support] using hq
      cases hm : M q a with
      | none =>
        simp [table,hm] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        simp [support]
      | some p =>
        cases p with
        | mk dst action =>
          simp [table,hm] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          have hd : dst ∈ states := h.2 (by rw [hm]; rfl) hq'
          simp [support,hd]

theorem embed_in_support [DecidableEq Λ] (states : Finset Λ) (c : TM0.Cfg Γ Λ)
    (h : c.q ∈ states) : (embed c).q ∈ support states := by
  simp [embed, support, h]

def system (M : TM0.Machine Γ Λ) (initial : TM0.Cfg Γ Λ) : EventSystem (TM0.Cfg Γ (Option Λ)) where
  initial := embed initial
  step c := ((TM0.step (table M) c).getD c, false)

/-- The totalized run matches every finite source prefix at exactly the same
transition index. -/
theorem run_matches (M : TM0.Machine Γ Λ) (initial final : TM0.Cfg Γ Λ) (n : Nat)
    (h : runSteps (TM0.step M) n initial = some final) :
    (system M initial).run n = embed final := by
  induction n generalizing final with
  | zero =>
    change some initial = some final at h
    cases Option.some.inj h
    rfl
  | succ n ih =>
    change (runSteps (TM0.step M) n initial).bind (TM0.step M) = some final at h
    cases hr : runSteps (TM0.step M) n initial with
    | none => simp [hr] at h
    | some mid =>
      have hm : TM0.step M mid = some final := by simpa [hr] using h
      rw [EventSystem.run_succ, ih mid hr]
      simp [system,step_live M mid final hm]

/-- A source halt is followed by one transition into an absorbing state;
the tape at the source halt is preserved at every subsequent time. -/
theorem terminal_run (M : TM0.Machine Γ Λ) (initial final : TM0.Cfg Γ Λ) (n : Nat)
    (h : runSteps (TM0.step M) n initial = some final) (ht : TM0.step M final = none) :
    ∀ k, (system M initial).run (n + 1 + k) = stopped final.Tape := by
  intro k
  induction k with
  | zero =>
    rw [Nat.add_zero,EventSystem.run_succ,run_matches M initial final n h]
    simp [system,step_terminal M final ht]
  | succ k ih =>
    rw [Nat.add_succ,EventSystem.run_succ,ih]
    simp [system,step_stopped]

/-- No transition in this evaluator adapter emits an event, including the
transition into the absorbing state. -/
theorem never_beeps (M : TM0.Machine Γ Λ) (initial : TM0.Cfg Γ Λ) (t : Nat) :
    ¬ (system M initial).BeepAt t := by simp [EventSystem.BeepAt,system]

theorem eventuallySilent (M : TM0.Machine Γ Λ) (initial : TM0.Cfg Γ Λ) :
    (system M initial).EventuallySilent := ⟨0, fun t _ => never_beeps M initial t⟩

end Shared.Beeping.TM0Totalize
