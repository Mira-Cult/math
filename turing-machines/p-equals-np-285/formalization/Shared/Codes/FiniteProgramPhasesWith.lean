import Shared.Codes.FiniteProgramPhaseProbe

/-! Generalize the existing fixed-count phase assembly to an arbitrary valid
finite continuation. This preserves full-tape equivalence and exact cost. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.Codes.FiniteProgramPhasesWith
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost result totalCost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramPhaseProbe (stride shiftStatus_add)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def phases (zero one : List Bool) (next : Program) : Nat → Program
  | 0 => next
  | n+1 => Shared.Codes.FiniteProgramSplice.program (Shared.Codes.FiniteProgramPhase.program zero one) (phases zero one next n)

theorem phases_valid (zero one : List Bool) (next : Program) (hn : valid next = true) (n : Nat) :
    valid (phases zero one next n) = true := by
  induction n with
  | zero => exact hn
  | succ n ih =>
    exact Shared.Codes.FiniteProgramSplice.program_valid _ _
      (Shared.Codes.FiniteProgramPhase.program_valid zero one) ih

theorem phases_length (zero one : List Bool) (next : Program) (n : Nat) :
    (phases zero one next n).length = n*stride zero one+next.length := by
  induction n with
  | zero => simp [phases]
  | succ n ih =>
    simp [phases,Shared.Codes.FiniteProgramSplice.program,Shared.Codes.FiniteProgramLink.link,
      Shared.Codes.FiniteProgramSplice.stem_length,ih,stride,Nat.add_mul,Nat.add_comm,Nat.add_left_comm]

theorem first_phase_related (zero one : List Bool) (next : Program) (n : Nat)
    (b p : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (p::L) b xs).2) :
    ∃ d, run (phases zero one next (n+1)) c (cost zero one b xs) = some (.inr d) ∧
      d.1 = stride zero one ∧ TapeRel d.2 (canonical L p (output zero one b xs)).2 := by
  let phase := Shared.Codes.FiniteProgramPhase.program zero one
  let rest := phases zero one next n
  have hp := Shared.Codes.FiniteProgramPhase.cycle zero one b false p xs L
  change run phase (canonical (p::L) b xs) (cost zero one b xs) =
    some (.inr (stride zero one,tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one b xs) ++ [false,false]))) at hp
  have hp' := Shared.Codes.FiniteProgramSplice.first_run phase rest
    (Shared.Codes.FiniteProgramPhase.program_valid zero one) (canonical (p::L) b xs) _ _ false
    (by simp [canonical,phase,Shared.Codes.FiniteProgramPhase.length])
    (Shared.Codes.FiniteProgramPhase.terminal_step zero one) hp
  change run (phases zero one next (n+1)) (canonical (p::L) b xs) _ = _ at hp'
  have h := run_related (phases zero one next (n+1)) c (canonical (p::L) b xs)
    (by simpa [canonical] using hq) ht (cost zero one b xs)
  rw [hp'] at h
  cases hs : run (phases zero one next (n+1)) c (cost zero one b xs) with
  | none => rw [hs] at h; exact False.elim h
  | some v => cases v with
    | inl out => rw [hs] at h; exact False.elim h
    | inr d =>
      rw [hs] at h
      have hd : d.1 = stride zero one ∧
          TapeRel d.2 (tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one b xs) ++ [false,false])) := h
      refine ⟨d,rfl,hd.1,?_⟩
      apply Eq.trans hd.2
      have hpad := Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank L
        (false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one b xs) ++ [false,false]) p
      change TapeRel (tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one b xs) ++ [false,false]))
        (canonical L p (output zero one b xs)).2
      simpa [canonical,List.append_assoc] using hpad

/-- The actual linked finite table executes the requested predecessor phases,
then reaches the arbitrary continuation with the entire tape specified. -/
theorem run_phases (zero one : List Bool) (next : Program) (hn : valid next = true)
    (n : Nat) (remaining : List Bool) (hlen : remaining.length = n) (b : Bool)
    (xs L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    ∃ d, run (phases zero one next n) c (totalCost zero one remaining b xs) = some (.inr d) ∧
      d.1 = n*stride zero one ∧ TapeRel d.2 (canonical L (result zero one remaining b xs).1
        (result zero one remaining b xs).2).2 := by
  induction n generalizing remaining b xs c with
  | zero =>
    have he : remaining = [] := List.length_eq_zero_iff.mp hlen
    subst remaining
    refine ⟨c,rfl,by simpa using hq,?_⟩
    simpa [result] using ht
  | succ n ih =>
    cases remaining with
    | nil => simp at hlen
    | cons p ps =>
      have hl : ps.length = n := by simp at hlen; omega
      have ht' : TapeRel c.2 (canonical (p::(ps++L)) b xs).2 := by simpa using ht
      obtain ⟨mid,hmid,hmidq,hmidt⟩ := first_phase_related zero one next n b p xs (ps++L) c hq ht'
      obtain ⟨last,hlast,hlastq,hlastt⟩ := ih ps hl p (output zero one b xs) (0,mid.2) rfl hmidt
      let phase := Shared.Codes.FiniteProgramPhase.program zero one
      let rest := phases zero one next n
      have hc : ((0,mid.2) : Config).1 < rest.length := by
        exact Shared.Codes.FiniteProgramLink.valid_nonempty rest (phases_valid zero one next hn n)
      have hs := Shared.Codes.FiniteProgramSplice.second_run phase rest (phases_valid zero one next hn n)
        (0,mid.2) hc (totalCost zero one ps p (output zero one b xs))
      rw [hlast] at hs
      refine ⟨shiftConfig (stride zero one) last,?_,?_,?_⟩
      · change run (phases zero one next (n+1)) c
          (cost zero one b xs + totalCost zero one ps p (output zero one b xs)) = _
        rw [run_continue _ _ _ _ _ hmid]
        have hcfg : mid = shiftConfig (stride zero one) (0,mid.2) := by
          cases mid with | mk q t => simp only at hmidq; subst q; rfl
        rw [hcfg]
        simpa [phase,rest,stride,shiftStatus,phases] using hs
      · simp only [shiftConfig,hlastq]
        simp [Nat.add_mul,Nat.add_comm]
      · exact hlastt

/-- Any finite run of the actual continuation is reproduced after relocation. -/
theorem continuation_run (zero one : List Bool) (next : Program) (hn : valid next = true)
    (n : Nat) (c : Config) (hc : c.1 < next.length) (fuel : Nat) :
    run (phases zero one next n) (shiftConfig (n*stride zero one) c) fuel =
      shiftStatus (n*stride zero one) (run next c fuel) := by
  induction n with
  | zero =>
    cases h : run next c fuel with
    | none => simp [phases,shiftConfig,shiftStatus,h]
    | some v => cases v <;> simp [phases,shiftConfig,shiftStatus,h]
  | succ n ih =>
    let phase := Shared.Codes.FiniteProgramPhase.program zero one
    let s := stride zero one
    have hin : (shiftConfig (n*s) c).1 < (phases zero one next n).length := by
      simp only [shiftConfig,phases_length,s]
      omega
    have h := Shared.Codes.FiniteProgramSplice.second_run phase (phases zero one next n)
      (phases_valid zero one next hn n) (shiftConfig (n*s) c) hin fuel
    rw [ih,shiftStatus_add] at h
    simpa [phase,s,stride,phases,shiftConfig,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end Shared.Codes.FiniteProgramPhasesWith
