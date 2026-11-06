import Shared.Codes.FiniteProgramTwoExit
import Shared.Codes.FiniteProgramThreeExit

/-! Replace one terminal row by a charged, tape-preserving handoff to a
relocated finite continuation. The other source rows are unchanged. -/
namespace Shared.Codes.FiniteProgramOneExit
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramThreeExit (bounce)

def program (p q : Program) (exit : Nat) : Program :=
  Shared.Codes.FiniteProgramTwoExit.program p q exit exit

def offset (p : Program) : Nat := p.length+2

@[simp] theorem program_length (p q : Program) (exit : Nat) :
    (program p q exit).length = offset p+q.length := by
  simp [program,offset,Shared.Codes.FiniteProgramTwoExit.program_length]

theorem program_valid (p q : Program) (exit : Nat)
    (hp : valid p = true) (hq : valid q = true) (he : exit < p.length) :
    valid (program p q exit) = true :=
  Shared.Codes.FiniteProgramTwoExit.program_valid p q exit exit hp hq he he

/-- Any source run reaching a live configuration is retained up to its first
entry into the replaced terminal row. -/
theorem first_entry (p q : Program) (exit : Nat) (c d : Config) (n : Nat)
    (hp : valid p = true) (hc : c.1 < p.length)
    (he : ∀ t, step p (exit,t) = some (.inl false))
    (hr : run p c n = some (.inr d)) : run (program p q exit) c n = some (.inr d) :=
  Shared.Codes.FiniteProgramTwoExit.first_entry p q exit exit c d n hp hc he he hr

/-- The handoff makes two real transitions and preserves the tape modulo
blank padding. -/
theorem handoff (p q : Program) (exit : Nat) (he : exit < p.length) (t : Tape) :
    run (program p q exit) (exit,t) 2 = some (.inr (offset p,bounce t)) := by
  have hr := Shared.Codes.FiniteProgramTwoExit.second_row p q exit exit he
  have hb := Shared.Codes.FiniteProgramTwoExit.second_bridge p q exit exit
  have h₁ : step (program p q exit) (exit,t) = some (.inr (p.length+1,moveTape false t.2.1 t)) := by
    cases ht : t.2.1 <;> simp [program,step,hr,branch,ht]
  have h₂ (u : Tape) : step (program p q exit) (p.length+1,u) =
      some (.inr (offset p,moveTape true u.2.1 u)) := by
    cases hu : u.2.1 <;> simp only [program,step,hb,bridge,offset,hu] <;> rfl
  change advance (program p q exit) (step (program p q exit) (exit,t)) = _
  rw [h₁]
  exact h₂ _

/-- The relocated continuation executes with no change in its step count. -/
theorem continuation (p q : Program) (exit : Nat) (hq : valid q = true)
    (c : Config) (hc : c.1 < q.length) (n : Nat) :
    run (program p q exit) (shiftConfig (offset p) c) n = shiftStatus (offset p) (run q c n) := by
  simpa [program,offset,Shared.Codes.FiniteProgramTwoExit.program,
    Shared.Codes.FiniteProgramTwoExit.pre_length] using
      Shared.Codes.FiniteProgramLink.run_shift (Shared.Codes.FiniteProgramTwoExit.pre p exit exit)
        q [] hq c hc n

end Shared.Codes.FiniteProgramOneExit
