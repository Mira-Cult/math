import Shared.Codes.FiniteProgramDropTag

/-! Move the separator across retained tagged data, then remove the next
metadata block. The number of retained data is fixed in the generated table. -/
namespace Shared.Codes.FiniteProgramCrossTag
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons tagged_append)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

/-- Row 8 is an unexecuted terminal continuation. Rows 0 through 7 move a
separator rightward across one tagged bit, retaining that bit. -/
def phase : Program :=
  [ ((false,true,1,0),(true,true,1,0)),
    ((true,true,2,0),(true,true,2,0)),
    ((false,true,3,0),(true,true,3,0)),
    ((true,false,4,0),(true,false,5,0)),
    ((false,true,6,0),(false,true,6,0)),
    ((true,true,6,0),(true,true,6,0)),
    ((false,true,7,0),(true,true,7,0)),
    ((false,false,8,0),(false,false,8,0)),
    ((false,true,0,1),(true,true,0,1)) ]

theorem phase_valid : valid phase = true := by decide

theorem phase_stop (t : Tape) : step phase (phase.length-1,t) = some (.inl false) := by
  cases h : t.2.1 <;> simp [phase,step,h]

/-- A retained triple is shifted left across the separator. The separator
is moved to the triple's right, so the preceding prefix is preserved. -/
theorem cross (b x : Bool) (xs L R : List Bool) :
    run phase (0,tapeAt L (b::false::tagged (x::xs) ++ false::R)) 7 =
      some (.inr (8,tapeAt (x::true::b::L) (true::false::tagged xs ++ false::R))) := by
  cases b <;> cases x <;> simp [phase,run,advance,step,tagged_cons,tapeAt,moveTape]

/-- Head and left tape after crossing a list of retained tagged data. -/
def cursor : Bool → List Bool → List Bool → Bool × List Bool
  | b, L, [] => (b,L)
  | b, L, x::xs => cursor true (x::true::b::L) xs

/-- The head together with its left tape contains the original source and
all retained triples, nearest cell first. -/
theorem cursor_contents (b : Bool) (L kept : List Bool) :
    (cursor b L kept).1 :: (cursor b L kept).2 = (tagged kept).reverse ++ b::L := by
  induction kept generalizing b L with
  | nil => rfl
  | cons x xs ih =>
    simpa [cursor,tagged_cons,List.reverse_cons,List.append_assoc] using ih true (x::true::b::L)

/-- The fixed table count pays for every retained triple, then executes the
existing finite metadata-removal table. -/
def program : Nat → Program
  | 0 => Shared.Codes.FiniteProgramDropTag.program
  | n+1 => Shared.Codes.FiniteProgramSplice.program phase (program n)

theorem program_valid (n : Nat) : valid (program n) = true := by
  induction n with
  | zero => exact Shared.Codes.FiniteProgramDropTag.program_valid
  | succ n ih => exact Shared.Codes.FiniteProgramSplice.program_valid phase _ phase_valid ih

theorem program_length (n : Nat) : (program n).length = 8*n+48 := by
  induction n with
  | zero => exact Shared.Codes.FiniteProgramDropTag.program_length
  | succ n ih =>
    simp [program,Shared.Codes.FiniteProgramSplice.program,Shared.Codes.FiniteProgramLink.link,
      Shared.Codes.FiniteProgramSplice.stem_length,phase,ih]
    omega

/-- Cross any fixed list of retained tagged data and delete the following
metadata triple. The tail remains tagged, and all physical steps are counted. -/
theorem cross_drop (kept rest L R : List Bool) (b metadata : Bool) :
    run (program kept.length)
      (0,tapeAt L (b::false::tagged (kept ++ metadata::rest) ++ false::R))
      (7*kept.length + 30*rest.length+20) =
      some (.inr (8*kept.length+47,
        tapeAt (cursor b L kept).2 ((cursor b L kept).1::false::tagged rest ++
          false::false::false::false::R))) := by
  induction kept generalizing b L with
  | nil =>
    simpa [program,cursor] using Shared.Codes.FiniteProgramDropTag.drop_first b metadata rest L R
  | cons x xs ih =>
    have hcross := cross b x (xs ++ metadata::rest) L R
    have hfirst := Shared.Codes.FiniteProgramSplice.first_run phase (program xs.length) phase_valid
      _ _ _ false (by simp [phase]) phase_stop hcross
    have hrec := ih (x::true::b::L) true
    have hshift := Shared.Codes.FiniteProgramSplice.second_run phase (program xs.length)
      (program_valid xs.length) (0,tapeAt (x::true::b::L)
        (true::false::tagged (xs ++ metadata::rest) ++ false::R))
      (by simp [program_length]) (7*xs.length+30*rest.length+20)
    rw [hrec] at hshift
    have htime : 7*(x::xs).length+30*rest.length+20 = 7+(7*xs.length+30*rest.length+20) := by simp; omega
    rw [htime]
    simp only [List.length_cons,List.cons_append,program]
    simp only [List.cons_append] at hfirst
    rw [run_continue _ _ _ _ _ hfirst]
    simpa [cursor,phase,shiftConfig,shiftStatus,Nat.mul_add,Nat.add_assoc,Nat.add_comm,
      Nat.add_left_comm] using hshift

open Shared.ComplexityBridge.FirstBlocksContent (frames frames_cons selected selected_length)

/-- Starting just after one metadata removal, cross that frame's selected
word and remove the next metadata block. This uses a table whose number of
states depends only on the fixed word width, not on the input length. -/
theorem cross_drop_frame (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (b previous next : Bool) (bits L R : List Bool) :
    let kept := selected zero one previous
    let remaining := selected zero one next ++ frames zero one bits
    run (program width)
      (0,tapeAt L (b::false::tagged (kept ++ frames zero one (next::bits)) ++ false::R))
      (7*width+30*(width+bits.length*(width+1))+20) =
      some (.inr (8*width+47,
        tapeAt (cursor b L kept).2 ((cursor b L kept).1::false::tagged remaining ++
          false::false::false::false::R))) := by
  have h := cross_drop (selected zero one previous)
    (selected zero one next ++ frames zero one bits) L R b next
  simpa [frames_cons,selected_length zero one width hzero hone,
    Shared.Codes.FiniteProgramDropTag.frames_length zero one bits width hzero hone] using h

namespace Fixtures
example : run phase (0,tapeAt [] [false,false,true,true,true,false]) 7 =
    some (.inr (8,tapeAt [true,true,false] [true,false,false])) := by decide
example : run (program 2)
    (0,tapeAt [] (false::false::tagged ([true,false] ++ true::[true]) ++ [false])) 64 =
    some (.inr (63,tapeAt (cursor false [] [true,false]).2
      ((cursor false [] [true,false]).1::false::tagged [true] ++ [false,false,false,false]))) := by decide
example : (program 2).length = 64 := by decide
end Fixtures

end Shared.Codes.FiniteProgramCrossTag
