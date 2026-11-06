import Shared.Codes.FiniteProgramOneExit

/-! Preserve live executions up to a terminal state whose Boolean result may
depend on the tape, then charge and execute the existing one-exit handoff. -/
namespace Shared.Codes.FiniteProgramTapeTerminal
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (run_in_range shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramThreeExit (bounce)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

/-- A live final source configuration cannot have visited a state that would
have returned a Boolean on its next step, even if that Boolean depends on the
specific tape present at the visit. -/
theorem not_visited_before (p : Program) (c last : Config) (n stop : Nat)
    (hstop : ∀ t, ∃ b, step p (stop,t) = some (.inl b))
    (hfinal : run p c n = some (.inr last)) :
    ∀ i < n, ∀ d, run p c i = some (.inr d) → d.1 ≠ stop := by
  intro i hi d hr he
  obtain ⟨b,hb⟩ := hstop d.2
  have hs : step p d = some (.inl b) := by
    cases d with
    | mk q t => simp only at he; subst q; exact hb
  have hnext : run p c (i+1) = some (.inl b) := by
    rw [run_succ,hr]
    exact hs
  have hend := run_result_stable p c (show i+1 ≤ n by omega) hnext
  rw [hend] at hfinal
  cases hfinal

/-- Replacing one terminal state preserves every source run ending live,
provided the two tables agree on the other reachable source states. -/
theorem first_entry_generic (p q : Program) (c last : Config) (n stop : Nat)
    (hvalid : valid p = true) (hc : c.1 < p.length)
    (hstop : ∀ t, ∃ b, step p (stop,t) = some (.inl b))
    (hsame : ∀ d, d.1 < p.length → d.1 ≠ stop → step p d = step q d)
    (hfinal : run p c n = some (.inr last)) : run q c n = some (.inr last) := by
  have hnot := not_visited_before p c last n stop hstop hfinal
  have heq : ∀ i ≤ n, run p c i = run q c i := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [run_succ,run_succ,← ih (by omega)]
      cases hr : run p c i with
      | none => rfl
      | some v => cases v with
        | inl b => rfl
        | inr d =>
          change step p d = step q d
          have hin := run_in_range p hvalid c hc i
          rw [hr] at hin
          exact hsame d hin (hnot i (by omega) d hr)
  rw [← heq n (by omega)]
  exact hfinal

/-- The existing one-exit table preserves the source run to its first live
terminal-state entry, for tape-dependent Boolean terminal rows. -/
theorem first_entry (p q : Program) (exit : Nat) (c d : Config) (n : Nat)
    (hp : valid p = true) (hc : c.1 < p.length)
    (he : ∀ t, ∃ b, step p (exit,t) = some (.inl b))
    (hr : run p c n = some (.inr d)) :
    run (Shared.Codes.FiniteProgramOneExit.program p q exit) c n = some (.inr d) := by
  apply first_entry_generic p (Shared.Codes.FiniteProgramOneExit.program p q exit)
    c d n exit hp hc he ?_ hr
  intro z hz hne
  exact Shared.Codes.FiniteProgramTwoExit.source_other p q exit exit z hz hne hne

/-- The existing one-exit adapter executes two physical transitions. -/
theorem handoff (p q : Program) (exit : Nat) (he : exit < p.length) (t : Tape) :
    run (Shared.Codes.FiniteProgramOneExit.program p q exit) (exit,t) 2 =
      some (.inr (Shared.Codes.FiniteProgramOneExit.offset p,bounce t)) :=
  Shared.Codes.FiniteProgramOneExit.handoff p q exit he t

/-- Source execution, the two-step handoff, and any finite number of steps
of a valid continuation compose to one exact run. No continuation termination
is assumed: the equality includes live, terminal, and invalid statuses. -/
theorem run_continuation (p q : Program) (exit : Nat) (c : Config) (t : Tape)
    (m n : Nat) (hp : valid p = true) (hq : valid q = true)
    (hc : c.1 < p.length) (he : exit < p.length)
    (hstop : ∀ u, ∃ b, step p (exit,u) = some (.inl b))
    (hr : run p c m = some (.inr (exit,t))) :
    run (Shared.Codes.FiniteProgramOneExit.program p q exit) c (m+2+n) =
      shiftStatus (Shared.Codes.FiniteProgramOneExit.offset p) (run q (0,bounce t) n) := by
  have hfirst := first_entry p q exit c (exit,t) m hp hc hstop hr
  rw [show m+2+n = m+(2+n) by omega,
    run_continue _ _ _ m _ hfirst,
    run_continue _ _ _ 2 _ (handoff p q exit he t)]
  have hcq : (0 : Nat) < q.length := Shared.Codes.FiniteProgramLink.valid_nonempty q hq
  simpa [shiftConfig] using
    (Shared.Codes.FiniteProgramOneExit.continuation p q exit hq (0,bounce t) hcq n)

/-- Relocating a finite-program status preserves its blank-tape relation. -/
theorem shiftStatus_related (offset : Nat) (a b : Status) (h : StatusRel a b) :
    StatusRel (shiftStatus offset a) (shiftStatus offset b) := by
  cases a with
  | none => cases b <;> simp [StatusRel,shiftStatus] at h ⊢
  | some av =>
    cases av with
    | inl x =>
      cases b with
      | none => simp [StatusRel] at h
      | some bv => cases bv with
        | inl y => simpa [StatusRel,shiftStatus] using h
        | inr z => simp [StatusRel] at h
    | inr x =>
      cases b with
      | none => simp [StatusRel] at h
      | some bv => cases bv with
        | inl y => simp [StatusRel] at h
        | inr y =>
          change offset+x.1 = offset+y.1 ∧ TapeRel x.2 y.2
          exact ⟨congrArg (offset+·) h.1,h.2⟩

/-- The bounce does not change the logical tape. The composed run is related
to the same finite continuation started on the original source tape. -/
theorem run_continuation_related (p q : Program) (exit : Nat) (c : Config) (t : Tape)
    (m n : Nat) (hp : valid p = true) (hq : valid q = true)
    (hc : c.1 < p.length) (he : exit < p.length)
    (hstop : ∀ u, ∃ b, step p (exit,u) = some (.inl b))
    (hr : run p c m = some (.inr (exit,t))) :
    StatusRel (run (Shared.Codes.FiniteProgramOneExit.program p q exit) c (m+2+n))
      (shiftStatus (Shared.Codes.FiniteProgramOneExit.offset p) (run q (0,t) n)) := by
  rw [run_continuation p q exit c t m n hp hq hc he hstop hr]
  apply shiftStatus_related
  exact run_related q (0,bounce t) (0,t) rfl
    (Shared.Codes.FiniteProgramThreeExit.bounce_related t) n

end Shared.Codes.FiniteProgramTapeTerminal
