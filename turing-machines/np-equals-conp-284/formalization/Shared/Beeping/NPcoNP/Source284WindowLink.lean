import Shared.Beeping.NPcoNP.Source284UnaryWindowVerifier
import Shared.Beeping.NPcoNP.Source284TaggedGuardCoverage

/-! Link a finite, executable loader table to a fixed finite verifier. The
loader must actually establish the bounded input window in polynomially many
source steps; that obligation is stated separately, not assumed proved. -/
namespace Shared.Beeping.NPcoNP.Source284WindowLink

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ListTables (Rows)

/-- Loader successors may stay in the prefix or enter the first verifier
state, but cannot jump into an arbitrary verifier state. -/
def LoaderClosed (rows : Rows) : Prop :=
  ∀ q, q < rows.length → ∀ b q',
    (Source284ListTables.table rows q b).next = some q' → q' ≤ rows.length

def table (rows : Rows) (verifier : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q < rows.length then Source284ListTables.table rows q b
  else shiftRow rows.length (verifier (q-rows.length) b)

def description (rows : Rows) (states : Nat) (verifier : Nat → Bool → Row) : Nat :=
  encode (rows.length+states) (table rows verifier) 1

theorem relocated_row (rows : Rows) (verifier : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table rows verifier (rows.length+q) b = shiftRow rows.length (verifier q b) := by
  simp [table]

theorem relocated_step (rows : Rows) (verifier : Nat → Bool → Row) (c : Config) :
    step (table rows verifier) (shiftConfig rows.length c) =
      shiftConfig rows.length (step verifier c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (rows : Rows) (verifier : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table rows verifier) (shiftConfig rows.length c) clock =
      shiftConfig rows.length (run verifier c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

theorem closed (rows : Rows) (states : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < states) (hl : LoaderClosed rows) (hv : Closed states verifier) :
    Closed (rows.length+states) (table rows verifier) := by
  intro q hq b q' hnext
  by_cases h : q < rows.length
  · have ht : q' ≤ rows.length := hl q h b q' (by simpa [table,h] using hnext)
    omega
  · have hq' : q-rows.length < states := by omega
    have he : (shiftRow rows.length (verifier (q-rows.length) b)).next = some q' := by
      simpa [table,h] using hnext
    cases hx : (verifier (q-rows.length) b).next with
    | none => simp [shiftRow,hx] at he
    | some target =>
      have htarget := hv (q-rows.length) hq' b target hx
      simp [shiftRow,hx] at he
      subst q'
      omega

/-- Once the loader reaches the first relocated verifier state, all later
source steps agree exactly, including the accepting transition. -/
theorem source_relocated (rows : Rows) (states : Nat) (verifier : Nat → Bool → Row)
    (left right clock : Nat) (hn : 0 < states) (hl : LoaderClosed rows)
    (hv : Closed states verifier) :
    ((Source284Relative.run (description rows states verifier)
      ⟨left,right,active rows.length⟩ clock).state == 0) =
    ((Source284Relative.run (encode states verifier 1) ⟨left,right,active 0⟩ clock).state == 0) := by
  have h1 : Valid (rows.length+states) (shiftConfig rows.length ⟨left,right,some 0⟩) := by
    intro q hq
    simp [shiftConfig] at hq
    subst q
    omega
  have h0 : Valid states ⟨left,right,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    exact hn
  have hr1 := run_toSource (rows.length+states) (table rows verifier) 1
    (shiftConfig rows.length ⟨left,right,some 0⟩) (closed rows states verifier hn hl hv) h1 clock
  have hr0 := run_toSource states verifier 1 ⟨left,right,some 0⟩ hv h0 clock
  change Source284Relative.run (description rows states verifier) ⟨left,right,active rows.length⟩ clock = _ at hr1
  change Source284Relative.run (encode states verifier 1) ⟨left,right,active 0⟩ clock = _ at hr0
  rw [hr1,hr0,relocated_run]
  cases h : (run verifier ⟨left,right,some 0⟩ clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

/-- A nonempty loader cannot reach the relocated verifier in zero steps. -/
theorem handoff_positive (rows : Rows) (states : Nat) (verifier : Nat → Bool → Row)
    (input certificate time left right : Nat) (hne : 0 < rows.length)
    (handoff : Source284Relative.run (description rows states verifier)
      (Source284Relative.initial input certificate) time = ⟨left,right,active rows.length⟩) :
    0 < time := by
  by_contra h
  have hz : time = 0 := by omega
  subst time
  have hs := congrArg Source284Relative.Config.state handoff
  change 1 = 2 * rows.length + 1 at hs
  omega

/-- The supplied loader execution and the verifier execution are both paid
in the source clock; neither initializes an implicit tape. -/
theorem source_after_handoff (rows : Rows) (states : Nat) (verifier : Nat → Bool → Row)
    (input certificate time left right clock : Nat)
    (hn : 0 < states) (hl : LoaderClosed rows) (hv : Closed states verifier)
    (handoff : Source284Relative.run (description rows states verifier)
      (Source284Relative.initial input certificate) time = ⟨left,right,active rows.length⟩) :
    Source284Relative.accepts (description rows states verifier) input certificate (time+clock) =
      ((Source284Relative.run (encode states verifier 1) ⟨left,right,active 0⟩ clock).state == 0) := by
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,handoff]
  exact source_relocated rows states verifier left right clock hn hl hv

namespace Fixtures

def rows : Rows := [(⟨false,false,some 1⟩,⟨true,false,some 1⟩)]
def accept (_ : Nat) (b : Bool) : Row := ⟨b,false,none⟩
def reject (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩

example : LoaderClosed rows := by
  intro q hq b q' hn
  have hq0 : q = 0 := by simp [rows] at hq; omega
  subst q
  cases b <;> simp [rows,Source284ListTables.table] at hn <;> omega

-- Both read branches enter the verifier after one paid step. The accepting
-- and rejecting continuations then have different outcomes at the next step.
example : Source284Relative.accepts (description rows 1 accept) 5 9 2 = true := by decide +kernel
example : Source284Relative.accepts (description rows 1 reject) 5 9 2 = false := by decide +kernel
example : Source284Relative.accepts (description rows 1 accept) 4 9 2 = true := by decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284WindowLink
