import Shared.Codes.FiniteProgramCrossTag

/-! A finite buffer-end probe joined to fixed-width crossing and metadata
removal. Each branch restores the head before entering its continuation. -/
namespace Shared.Codes.FiniteProgramFrameProbe
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons)
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramCrossTag (phase phase_valid phase_stop cross cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def dummy : Row × Row := ((false,true,0,1),(true,true,0,1))

/-- A marker true two cells to the right enters state 5; false enters 53.
The probe restores the source head in either case. -/
def pre : Program :=
  [ ((false,true,1,0),(true,true,1,0)),
    ((false,true,2,0),(true,true,2,0)),
    ((false,false,4,0),(true,false,3,0)),
    ((false,false,5,0),(true,false,5,0)),
    ((false,false,53,0),(true,false,53,0)) ]

def base : Program := link pre Shared.Codes.FiniteProgramDropTag.program [dummy]

theorem base_length : base.length = 54 := by
  simp [base,link,pre,Shared.Codes.FiniteProgramDropTag.program_length]

theorem base_valid : valid base = true := by decide

theorem probe_empty (b : Bool) (L R : List Bool) :
    run base (0,tapeAt L (b::false::false::R)) 4 =
      some (.inr (53,tapeAt L (b::false::false::R))) := by
  cases b <;> simp [base,link,pre,run,advance,step,tapeAt,moveTape]

theorem probe_present (b m : Bool) (xs L R : List Bool) :
    run base (0,tapeAt L (b::false::tagged (m::xs) ++ false::R)) 4 =
      some (.inr (5,tapeAt L (b::false::tagged (m::xs) ++ false::R))) := by
  cases b <;> simp [base,link,pre,run,advance,step,tagged_cons,tapeAt,moveTape]

theorem remove_present (b m : Bool) (xs L R : List Bool) :
    run base (0,tapeAt L (b::false::tagged (m::xs) ++ false::R)) (30*xs.length+24) =
      some (.inr (52,tapeAt L (b::false::tagged xs ++ false::false::false::false::R))) := by
  rw [show 30*xs.length+24 = 4+(30*xs.length+20) by omega]
  rw [run_continue _ _ _ _ _ (probe_present b m xs L R)]
  have h := run_shift pre Shared.Codes.FiniteProgramDropTag.program [dummy]
    Shared.Codes.FiniteProgramDropTag.program_valid
    (0,tapeAt L (b::false::tagged (m::xs) ++ false::R))
    (by simp [Shared.Codes.FiniteProgramDropTag.program_length]) (30*xs.length+20)
  rw [Shared.Codes.FiniteProgramDropTag.drop_first] at h
  simpa [base,pre,shiftConfig,shiftStatus] using h

def cost : List Bool → Nat
  | [] => 4
  | _::xs => 30*xs.length+24

def result (b : Bool) (L R : List Bool) : List Bool → Config
  | [] => (53,tapeAt L (b::false::false::R))
  | _::xs => (52,tapeAt L (b::false::tagged xs ++ false::false::false::false::R))

theorem base_run (todo : List Bool) (b : Bool) (L R : List Bool) :
    run base (0,tapeAt L (b::false::tagged todo ++ false::R)) (cost todo) =
      some (.inr (result b L R todo)) := by
  cases todo with
  | nil => simpa [cost,result,Shared.Codes.FiniteProgramBitShuttle.tagged] using probe_empty b L R
  | cons m xs => simpa [cost,result] using remove_present b m xs L R

/-- One copy of the crossing phase per retained bit, followed by the actual
probe and removal program. -/
def program : Nat → Program
  | 0 => base
  | n+1 => Shared.Codes.FiniteProgramSplice.program phase (program n)

theorem program_valid (n : Nat) : valid (program n) = true := by
  induction n with
  | zero => exact base_valid
  | succ n ih => exact Shared.Codes.FiniteProgramSplice.program_valid phase _ phase_valid ih

theorem program_length (n : Nat) : (program n).length = 8*n+54 := by
  induction n with
  | zero => exact base_length
  | succ n ih =>
    simp [program,Shared.Codes.FiniteProgramSplice.program,link,
      Shared.Codes.FiniteProgramSplice.stem_length,phase,ih]
    omega

/-- After crossing `kept`, the table detects whether another tagged datum
exists. It removes that datum when present and otherwise exits at the empty
continuation. The entire run is finite and has the stated exact cost. -/
theorem cross_probe (kept todo L R : List Bool) (b : Bool) :
    run (program kept.length) (0,tapeAt L (b::false::tagged (kept ++ todo) ++ false::R))
      (7*kept.length+cost todo) =
      some (.inr (8*kept.length+(result (cursor b L kept).1 (cursor b L kept).2 R todo).1,
        (result (cursor b L kept).1 (cursor b L kept).2 R todo).2)) := by
  induction kept generalizing b L with
  | nil => simpa [program,cursor] using base_run todo b L R
  | cons x xs ih =>
    have hcross := cross b x (xs ++ todo) L R
    have hfirst := Shared.Codes.FiniteProgramSplice.first_run phase (program xs.length) phase_valid
      _ _ _ false (by simp [phase]) phase_stop hcross
    have hrec := ih (x::true::b::L) true
    have hshift := Shared.Codes.FiniteProgramSplice.second_run phase (program xs.length)
      (program_valid xs.length) (0,tapeAt (x::true::b::L)
        (true::false::tagged (xs ++ todo) ++ false::R))
      (by simp [program_length]) (7*xs.length+cost todo)
    rw [hrec] at hshift
    have htime : 7*(x::xs).length+cost todo = 7+(7*xs.length+cost todo) := by simp; omega
    rw [htime]
    simp only [List.length_cons,List.cons_append,program]
    simp only [List.cons_append] at hfirst
    rw [run_continue _ _ _ _ _ hfirst]
    simpa [cursor,phase,shiftConfig,shiftStatus,Nat.mul_add,Nat.add_assoc,Nat.add_comm,
      Nat.add_left_comm] using hshift

/-- Both branches return the head to its source cell. These are separate
live continuation states, not claims about halting the final machine. -/
theorem cross_empty (kept L R : List Bool) (b : Bool) :
    run (program kept.length) (0,tapeAt L (b::false::tagged kept ++ false::R))
      (7*kept.length+4) =
      some (.inr (8*kept.length+53,
        tapeAt (cursor b L kept).2 ((cursor b L kept).1::false::false::R))) := by
  simpa [cost,result] using cross_probe kept [] L R b

theorem cross_present (kept xs L R : List Bool) (b m : Bool) :
    run (program kept.length) (0,tapeAt L (b::false::tagged (kept ++ m::xs) ++ false::R))
      (7*kept.length+30*xs.length+24) =
      some (.inr (8*kept.length+52,
        tapeAt (cursor b L kept).2 ((cursor b L kept).1::false::tagged xs ++
          false::false::false::false::R))) := by
  simpa [cost,result,Nat.add_assoc] using cross_probe kept (m::xs) L R b

namespace Fixtures
example : run base (0,tapeAt [] [false,false,false]) 4 =
    some (.inr (53,tapeAt [] [false,false,false])) := by decide
example : run base (0,tapeAt [] [true,false,true,false,true,false]) 4 =
    some (.inr (5,tapeAt [] [true,false,true,false,true,false])) := by decide
example : run (program 1) (0,tapeAt [] [false,false,true,true,true,false]) 11 =
    some (.inr (61,tapeAt [true,true,false] [true,false,false])) := by
  simpa [cursor,Shared.Codes.FiniteProgramBitShuttle.tagged] using cross_empty [true] [] [] false
example : (program 1).length = 62 := by decide
end Fixtures

end Shared.Codes.FiniteProgramFrameProbe
