import Shared.Codes.FiniteProgramFork
import Shared.Codes.FiniteProgramProtectedMarkerPeek
import Shared.Codes.FiniteProgramAppendSkipFixed

/-! One protected output block is processed by a single finite table: peek
and retain its marker, append its data bit, and skip its fixed-width payload,
marker and occupancy cells. The two marker values end at different terminal
placeholders. The input layout is assumed, not validated by this table. -/
namespace Shared.Codes.FiniteProgramProtectedCompressStep
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def source (w : Nat) : Program := Shared.Codes.FiniteProgramProtectedMarkerPeek.program w
def worker (w : Nat) : Program := Shared.Codes.FiniteProgramAppendSkipFixed.program (w+2)
def exit (w : Nat) (marked : Bool) : Nat :=
  Shared.Codes.FiniteProgramProtectedMarkerPeek.state (2*w+2)
    (Shared.Codes.FiniteProgramProtectedMarkerPeek.flag marked)
def program (w : Nat) : Program := Shared.Codes.FiniteProgramFork.program (source w) (worker w) (worker w)
  (exit w false) (exit w true)
def entry (w : Nat) (marked : Bool) : Nat :=
  if marked then Shared.Codes.FiniteProgramFork.off₁ (source w) (worker w)
  else Shared.Codes.FiniteProgramFork.off₀ (source w)
def finish (w : Nat) (marked : Bool) : Nat :=
  entry w marked+Shared.Codes.FiniteProgramAppendSkip.offset+17*(w+2)

theorem program_valid (w : Nat) : valid (program w) = true :=
  Shared.Codes.FiniteProgramFork.program_valid _ _ _ _ _
    (Shared.Codes.FiniteProgramProtectedMarkerPeek.program_valid w)
    (Shared.Codes.FiniteProgramAppendSkipFixed.program_valid (w+2))
    (Shared.Codes.FiniteProgramAppendSkipFixed.program_valid (w+2))

/-- The two worker copies retain the source marker in their state numbers. -/
theorem finish_distinct (w : Nat) : finish w false ≠ finish w true := by
  have hw : 0 < (worker w).length := by
    simp [worker]
  simp only [finish,entry,Bool.false_eq_true,if_false,if_true,Shared.Codes.FiniteProgramFork.off₁]
  omega

@[simp] theorem program_length (w : Nat) : (program w).length = 38*w+160 := by
  simp [program,Shared.Codes.FiniteProgramFork.program_length,Shared.Codes.FiniteProgramFork.off₀,
    Shared.Codes.FiniteProgramFork.off₁,source,worker,
    Shared.Codes.FiniteProgramAppendSkipFixed.offset_value]
  omega

theorem exit_bound (w : Nat) (marked : Bool) : exit w marked < (source w).length :=
  Shared.Codes.FiniteProgramProtectedMarkerPeek.state_bound w (2*w+2) _ (by omega)

theorem exit_placeholder (w : Nat) (marked : Bool) (t : Tape) :
    step (source w) (exit w marked,t) = some (.inl false) :=
  Shared.Codes.FiniteProgramProtectedMarkerPeek.terminal_placeholder w marked t

theorem exit_distinct (w : Nat) : exit w false ≠ exit w true :=
  Shared.Codes.FiniteProgramProtectedMarkerPeek.marker_states_distinct w

/-- The charged handoff selects a different worker copy for each marker. -/
theorem handoff (w : Nat) (marked : Bool) (t : Tape) :
    run (program w) (exit w marked,t) 2 =
      some (.inr (entry w marked,Shared.Codes.FiniteProgramThreeExit.bounce t)) := by
  cases marked with
  | false =>
    simpa [program,entry] using Shared.Codes.FiniteProgramFork.handoff_first
      (source w) (worker w) (worker w) (exit w false) (exit w true)
      (exit_bound w false) (exit_distinct w) t
  | true =>
    simpa [program,entry] using Shared.Codes.FiniteProgramFork.handoff_second
      (source w) (worker w) (worker w) (exit w false) (exit w true) (exit_bound w true) t

theorem continuation (w : Nat) (marked : Bool) (c : Config) (hc : c.1 < (worker w).length) (n : Nat) :
    run (program w) (shiftConfig (entry w marked) c) n =
      shiftStatus (entry w marked) (run (worker w) c n) := by
  cases marked with
  | false =>
    simpa [program,entry] using Shared.Codes.FiniteProgramFork.continuation_first
      (source w) (worker w) (worker w) (exit w false) (exit w true)
      (Shared.Codes.FiniteProgramAppendSkipFixed.program_valid (w+2)) c hc n
  | true =>
    simpa [program,entry] using Shared.Codes.FiniteProgramFork.continuation_second
      (source w) (worker w) (worker w) (exit w false) (exit w true)
      (Shared.Codes.FiniteProgramAppendSkipFixed.program_valid (w+2)) c hc n

theorem finalHead_append (xs : List Bool) (b p : Bool) :
    Shared.Codes.FiniteProgramTaggedSkip.finalHead (xs++[b]) p = b := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simpa [Shared.Codes.FiniteProgramTaggedSkip.finalHead] using ih x

/-- A nonempty protected block followed by another data cell is processed
with the marker retained in the final state and the current data bit appended.
The occupied bit is assumed true but is not inspected. -/
theorem compress_block (w : Nat) (data marked next : Bool) (payload L xs : List Bool)
    (hlen : payload.length = w) :
    ∃ t, run (program w) (canonical (payload ++ marked::true::next::L) data xs)
        ((2*w+2)+2+((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7))) =
        some (.inr (finish w marked,t)) ∧
      TapeRel t (canonical L next (xs++[data])).2 := by
  obtain ⟨first,rest,hpad⟩ : ∃ first rest, first::rest = payload ++ [marked,true] := by
    cases payload with
    | nil => exact ⟨marked,[true],rfl⟩
    | cons b bs => exact ⟨b,bs++[marked,true],rfl⟩
  let remaining := rest++[next]
  have hremaining : remaining.length = w+2 := by
    have h := congrArg List.length hpad
    simp only [List.length_cons,List.length_append,List.length_cons,List.length_nil] at h
    dsimp [remaining]
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  have hleft : first::(remaining++L) = payload ++ marked::true::next::L := by
    dsimp [remaining]
    rw [List.append_assoc]
    change (first::rest) ++ (next::L) = _
    rw [hpad]
    simp [List.append_assoc]
  have hlast : Shared.Codes.FiniteProgramTaggedSkip.finalHead remaining first = next :=
    finalHead_append rest next first
  let input := canonical (payload ++ marked::true::next::L) data xs
  have hpeek := Shared.Codes.FiniteProgramProtectedMarkerPeek.peek_protected w data marked payload (next::L) xs hlen
  have hp := Shared.Codes.FiniteProgramFork.first_entry (source w) (worker w) (worker w)
    (exit w false) (exit w true) input (exit w marked,input.2) (2*w+2)
    (Shared.Codes.FiniteProgramProtectedMarkerPeek.program_valid w)
    (by simp [input,canonical,source]) (exit_placeholder w false) (exit_placeholder w true)
    (by simpa [input,source,exit] using hpeek)
  have hh := handoff w marked input.2
  have ht : TapeRel (Shared.Codes.FiniteProgramThreeExit.bounce input.2)
      (canonical (first::(remaining++L)) data xs).2 := by
    simpa [input,hleft] using Shared.Codes.FiniteProgramThreeExit.bounce_related input.2
  obtain ⟨t,hw,hrel⟩ := Shared.Codes.FiniteProgramAppendSkipFixed.append_then_skip_related
    remaining data first xs L (0,Shared.Codes.FiniteProgramThreeExit.bounce input.2) rfl ht
  have hw' : run (worker w) (0,Shared.Codes.FiniteProgramThreeExit.bounce input.2)
      ((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7)) =
      some (.inr (Shared.Codes.FiniteProgramAppendSkip.offset+17*(w+2),t)) := by
    simpa [worker,hremaining] using hw
  have hc := continuation w marked (0,Shared.Codes.FiniteProgramThreeExit.bounce input.2)
    (by simp [worker])
    ((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7))
  rw [hw'] at hc
  refine ⟨t,?_,?_⟩
  · change run (Shared.Codes.FiniteProgramFork.program (source w) (worker w) (worker w)
      (exit w false) (exit w true)) input _ = _
    rw [show (2*w+2)+2+((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7)) =
      (2*w+2)+(2+((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7))) by omega,
      run_continue _ _ _ _ _ hp]
    change run (program w) (exit w marked,input.2) _ = _
    rw [run_continue _ _ _ _ _ hh]
    simpa [finish,shiftConfig,shiftStatus,Nat.add_assoc] using hc
  · simpa [hlast] using hrel

/-- The final marker-specific state is a terminal placeholder. Later
compilation must replace both placeholders by suitable live continuations. -/
theorem finish_placeholder (w : Nat) (marked : Bool) (t : Tape) :
    step (program w) (finish w marked,t) = some (.inl false) := by
  have hc := continuation w marked
    (Shared.Codes.FiniteProgramAppendSkip.offset+17*(w+2),t)
    (by simp [worker]) 1
  have hw : run (worker w) (Shared.Codes.FiniteProgramAppendSkip.offset+17*(w+2),t) 1 =
      some (.inl false) := by
    simpa [worker,run,advance] using
      Shared.Codes.FiniteProgramAppendSkipFixed.terminal_placeholder (w+2) t
  rw [hw] at hc
  simpa [finish,run,advance,shiftConfig,shiftStatus,Nat.add_assoc] using hc

/-- The same block pass works from a blank-equivalent input representation. -/
theorem compress_block_related (w : Nat) (data marked next : Bool) (payload L xs : List Bool)
    (hlen : payload.length = w) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (payload ++ marked::true::next::L) data xs).2) :
    ∃ t, run (program w) c
        ((2*w+2)+2+((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7))) =
        some (.inr (finish w marked,t)) ∧
      TapeRel t (canonical L next (xs++[data])).2 := by
  obtain ⟨u,hu,hurel⟩ := compress_block w data marked next payload L xs hlen
  have hr := Shared.Codes.FiniteProgramTapeEquiv.run_related (program w) c
    (canonical (payload ++ marked::true::next::L) data xs) (by simpa [canonical] using hq) ht
    ((2*w+2)+2+((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7)))
  rw [hu] at hr
  cases h : run (program w) c
      ((2*w+2)+2+((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7))) with
  | none => rw [h] at hr; exact False.elim hr
  | some v => cases v with
    | inl out => rw [h] at hr; exact False.elim hr
    | inr d =>
      rcases d with ⟨q,t⟩
      rw [h] at hr
      change q = finish w marked ∧ TapeRel t u at hr
      refine ⟨t,?_,hr.2.trans hurel⟩
      simpa [hr.1] using h

end Shared.Codes.FiniteProgramProtectedCompressStep
