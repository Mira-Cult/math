import Shared.Codes.FiniteProgramTaggedSkip
import Shared.Codes.FiniteProgramOneExit

/-! Compile a fixed number of tagged-buffer skips into finite control. Each
stage has its own charged handoff; the final state is a terminal placeholder
for a later continuation. The erased cells must already be expendable. -/
namespace Shared.Codes.FiniteProgramTaggedSkipFixed
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramTaggedLoop (canonical tapeAt_append_blank)
open Shared.Codes.FiniteProgramTaggedSkip (base stop finalHead)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def program : Nat → Program
  | 0 => [stop]
  | n+1 => Shared.Codes.FiniteProgramOneExit.program base (program n) 14

@[simp] theorem program_length (n : Nat) : (program n).length = 17*n+1 := by
  induction n with
  | zero => simp [program]
  | succ n ih =>
    simp [program,Shared.Codes.FiniteProgramOneExit.program_length,
      Shared.Codes.FiniteProgramOneExit.offset,ih]
    omega

theorem program_valid (n : Nat) : valid (program n) = true := by
  induction n with
  | zero => decide
  | succ n ih =>
    exact Shared.Codes.FiniteProgramOneExit.program_valid base (program n) 14
      Shared.Codes.FiniteProgramTaggedSkip.base_valid ih (by simp)

/-- The final continuation state is an explicit terminal placeholder. A later
compiler must replace it with the appropriate live continuation. -/
theorem terminal_placeholder (n : Nat) (t : Tape) :
    step (program n) (17*n,t) = some (.inl false) := by
  induction n with
  | zero =>
    cases h : t.2.1 <;> simp [program,step,stop,h]
  | succ n ih =>
    have h := Shared.Codes.FiniteProgramOneExit.continuation base (program n) 14
      (program_valid n) (17*n,t) (by simp [program_length]) 1
    have hr : run (program n) (17*n,t) 1 = some (.inl false) := by
      simpa [run,advance] using ih
    rw [hr] at h
    simpa [program,run,advance,shiftConfig,shiftStatus,
      Shared.Codes.FiniteProgramOneExit.offset,Nat.mul_succ,Nat.add_comm] using h

/-- On any blank-equivalent input tape, exactly one stage advances to its
relocated continuation, shifting the unchanged buffer one cell left. -/
theorem stage (n : Nat) (b p : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (p::L) b xs).2) :
    ∃ t, run (program (n+1)) c (10*xs.length+7) = some (.inr (17,t)) ∧
      TapeRel t (canonical L p xs).2 := by
  let u := tapeAt L (p::false::tagged xs ++ [false,false,false,false])
  have hb := Shared.Codes.FiniteProgramTaggedAdvance.advance [stop] b p xs L [false,false]
  have hb' : run base (canonical (p::L) b xs) (10*xs.length+5) = some (.inr (14,u)) := by
    change run base (canonical (p::L) b xs) (10*xs.length+5) =
      some (.inr (14,tapeAt L (p::false::tagged xs ++ [false,false,false,false])))
    exact hb
  have hs := Shared.Codes.FiniteProgramOneExit.first_entry base (program n) 14
    (canonical (p::L) b xs) (14,u) (10*xs.length+5)
    Shared.Codes.FiniteProgramTaggedSkip.base_valid (by simp [canonical])
    Shared.Codes.FiniteProgramTaggedSkip.base_stop hb'
  have hh := Shared.Codes.FiniteProgramOneExit.handoff base (program n) 14 (by simp) u
  have hrun : run (program (n+1)) (canonical (p::L) b xs) (10*xs.length+7) =
      some (.inr (17,Shared.Codes.FiniteProgramThreeExit.bounce u)) := by
    change run (Shared.Codes.FiniteProgramOneExit.program base (program n) 14) _ _ = _
    rw [show 10*xs.length+7 = (10*xs.length+5)+2 by omega,
      run_continue _ _ _ _ _ hs]
    simpa [Shared.Codes.FiniteProgramOneExit.offset] using hh
  have htape : TapeRel (Shared.Codes.FiniteProgramThreeExit.bounce u) (canonical L p xs).2 := by
    apply Eq.trans (Shared.Codes.FiniteProgramThreeExit.bounce_related u)
    have hp := tapeAt_append_blank L (false::tagged xs ++ [false,false,false]) p
    simpa [u,canonical,List.append_assoc,TapeRel] using hp.symm
  have hr := run_related (program (n+1)) c (canonical (p::L) b xs)
    (by simpa [canonical] using hq) ht (10*xs.length+7)
  rw [hrun] at hr
  cases h : run (program (n+1)) c (10*xs.length+7) with
  | none => rw [h] at hr; exact False.elim hr
  | some v => cases v with
    | inl out => rw [h] at hr; exact False.elim hr
    | inr d =>
      rcases d with ⟨q,t⟩
      rw [h] at hr
      change q = 17 ∧ TapeRel t (Shared.Codes.FiniteProgramThreeExit.bounce u) at hr
      refine ⟨t,?_,hr.2.trans htape⟩
      simpa [hr.1] using h

/-- A table generated for exactly `remaining.length` skips reaches its
final continuation in a fixed number of actual transitions. No runtime fuel
or external stopping decision is used to select the continuation. -/
theorem skips (remaining : List Bool) (b : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    ∃ t, run (program remaining.length) c (remaining.length*(10*xs.length+7)) =
        some (.inr (17*remaining.length,t)) ∧
      TapeRel t (canonical L (finalHead remaining b) xs).2 := by
  induction remaining generalizing b c with
  | nil =>
    refine ⟨c.2,?_,?_⟩
    · cases c with
      | mk state tape => simp only at hq; subst state; simp
    · simpa [finalHead] using ht
  | cons p ps ih =>
    have ht' : TapeRel c.2 (canonical (p::(ps++L)) b xs).2 := by simpa using ht
    obtain ⟨u,hu,hurel⟩ := stage ps.length b p xs (ps++L) c hq ht'
    change run (Shared.Codes.FiniteProgramOneExit.program base (program ps.length) 14) c
      (10*xs.length+7) = some (.inr (17,u)) at hu
    obtain ⟨v,hv,hvrel⟩ := ih p (0,u) rfl hurel
    have hcont := Shared.Codes.FiniteProgramOneExit.continuation base (program ps.length) 14
      (program_valid ps.length) (0,u) (by simp) (ps.length*(10*xs.length+7))
    rw [hv] at hcont
    refine ⟨v,?_,?_⟩
    · change run (Shared.Codes.FiniteProgramOneExit.program base (program ps.length) 14) c
        ((ps.length+1)*(10*xs.length+7)) = _
      rw [show (ps.length+1)*(10*xs.length+7) =
        (10*xs.length+7)+ps.length*(10*xs.length+7) by simp [Nat.add_mul,Nat.add_comm],
        run_continue _ _ _ _ _ hu]
      simpa [shiftConfig,shiftStatus,Shared.Codes.FiniteProgramOneExit.offset,Nat.mul_succ,
        Nat.add_comm] using hcont
    · simpa [finalHead] using hvrel

end Shared.Codes.FiniteProgramTaggedSkipFixed
