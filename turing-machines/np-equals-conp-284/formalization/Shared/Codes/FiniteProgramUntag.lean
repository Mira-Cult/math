import Shared.Codes.FiniteProgramDropTag
import Shared.Codes.FiniteProgramCrossTag

/-! A finite-table pass that converts tagged bits to raw bits in place.
The head marks the last raw bit; a false separator precedes the remaining
self-delimited tagged buffer. -/
namespace Shared.Codes.FiniteProgramUntag
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons)
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def dummy : Row × Row := ((false,true,0,1),(true,true,0,1))

/-- At state 2, false detects the buffer end; true enters the local copy.
State 12 is the unexecuted empty continuation, and 13 enters two shifts. -/
def pre : Program :=
  [ ((false,true,1,0),(true,true,1,0)),
    ((false,true,2,0),(true,true,2,0)),
    ((false,false,11,0),(true,true,3,0)),
    ((false,false,4,0),(true,false,5,0)),
    ((false,false,6,0),(false,false,6,0)),
    ((false,false,7,0),(false,false,7,0)),
    ((false,true,8,0),(false,true,8,0)),
    ((true,true,8,0),(true,true,8,0)),
    ((false,true,9,0),(true,true,9,0)),
    ((false,true,10,0),(true,true,10,0)),
    ((false,false,13,0),(false,false,13,0)),
    ((false,false,12,0),(true,false,12,0)),
    dummy ]

def base : Program := link pre (Shared.Codes.FiniteProgramDropTag.phases 2) []

theorem base_length : base.length = 42 := by
  simp [base,link,pre,Shared.Codes.FiniteProgramDropTag.phases_length]

theorem base_valid : valid base = true := by decide

theorem prepare (b x : Bool) (xs L R : List Bool) :
    run base (0,tapeAt L (b::false::tagged (x::xs) ++ false::R)) 9 =
      some (.inr (13,tapeAt (false::x::b::L) (x::false::tagged xs ++ false::R))) := by
  cases b <;> cases x <;> simp [base,link,pre,run,advance,step,tagged_cons,tapeAt,moveTape]

theorem empty_run (b : Bool) (L R : List Bool) :
    run base (0,tapeAt L (b::false::false::R)) 4 =
      some (.inr (12,tapeAt L (b::false::false::R))) := by
  cases b <;> simp [base,link,pre,run,advance,step,tapeAt,moveTape]

theorem shifts (b x : Bool) (xs L R : List Bool) :
    run (Shared.Codes.FiniteProgramDropTag.phases 2)
      (0,tapeAt (false::x::b::L) (x::false::tagged xs ++ false::R)) (2*(10*xs.length+5)) =
      some (.inr (28,tapeAt (b::L) (x::false::tagged xs ++ false::false::false::R))) := by
  let cost := 10*xs.length+5
  have h₁ := Shared.Codes.FiniteProgramDropTag.first_phase 1 x false xs (x::b::L) R
  have h₂ := Shared.Codes.FiniteProgramDropTag.first_phase 0 false x xs (b::L) (false::R)
  have hs := Shared.Codes.FiniteProgramDropTag.rest_phase 1
    (0,tapeAt (x::b::L) (false::false::tagged xs ++ false::false::R))
    (by simp [Shared.Codes.FiniteProgramDropTag.phases_length]) cost
  rw [h₂] at hs
  rw [show 2*(10*xs.length+5) = cost+cost by simp [cost]; omega,run_continue _ _ _ _ _ h₁]
  simpa [shiftConfig,shiftStatus,cost] using hs

theorem base_cycle (b x : Bool) (xs L R : List Bool) :
    run base (0,tapeAt L (b::false::tagged (x::xs) ++ false::R)) (20*xs.length+19) =
      some (.inr (41,tapeAt (b::L) (x::false::tagged xs ++ false::false::false::R))) := by
  rw [show 20*xs.length+19 = 9+2*(10*xs.length+5) by omega]
  rw [run_continue _ _ _ _ _ (prepare b x xs L R)]
  have h := run_shift pre (Shared.Codes.FiniteProgramDropTag.phases 2) []
    (Shared.Codes.FiniteProgramDropTag.phases_valid 2)
    (0,tapeAt (false::x::b::L) (x::false::tagged xs ++ false::R))
    (by simp [Shared.Codes.FiniteProgramDropTag.phases_length]) (2*(10*xs.length+5))
  rw [shifts] at h
  simpa [base,pre,shiftConfig,shiftStatus] using h

theorem base_stop (t : Tape) : step base (41,t) = some (.inl false) := by
  have hr : base[41]? = some ((false,true,41,1),(true,true,41,1)) := by decide
  cases h : t.2.1 <;> simp [step,hr,h]

/-- Replace the cycle's terminal row with a two-step return to the entry.
The empty continuation at state 12 remains separate. -/
def program : Program := base.set 41 (branch 42) ++ [bridge 0]

theorem program_length : program.length = 43 := by simp [program,base_length]
theorem program_valid : valid program = true := by decide

theorem base_other (d : Config) (hd : d.1 < base.length) (hne : d.1 ≠ 41) :
    step base d = step program d := by
  have h : program[d.1]? = base[d.1]? := by
    simp [program,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,h]

theorem restart (b : Bool) (L R : List Bool) :
    run program (41,tapeAt L (b::false::R)) 2 = some (.inr (0,tapeAt L (b::false::R))) := by
  have h₁ : program[41]? = some (branch 42) := by simp [program,base_length]
  have h₂ : program[42]? = some (bridge 0) := by simp [program,base_length]
  cases b <;> simp [run,advance,step,h₁,h₂,branch,bridge,tapeAt,moveTape]

/-- Convert one tagged bit to one raw bit and return to the loop entry. -/
theorem cycle (b x : Bool) (xs L R : List Bool) :
    run program (0,tapeAt L (b::false::tagged (x::xs) ++ false::R)) (20*xs.length+21) =
      some (.inr (0,tapeAt (b::L) (x::false::tagged xs ++ false::false::false::R))) := by
  have h := Shared.Codes.FiniteProgramFirstEntry.first_entry base program _ _ _ 41 false
    base_valid (by simp [base_length]) base_stop base_other (base_cycle b x xs L R)
  rw [show 20*xs.length+21 = (20*xs.length+19)+2 by omega,run_continue _ _ _ _ _ h]
  simp only [List.cons_append]
  exact restart x (b::L) (tagged xs ++ false::false::false::R)

theorem finish (b : Bool) (L R : List Bool) :
    run program (0,tapeAt L (b::false::false::R)) 4 =
      some (.inr (12,tapeAt L (b::false::false::R))) := by
  exact Shared.Codes.FiniteProgramFirstEntry.first_entry base program _ _ _ 41 false
    base_valid (by simp [base_length]) base_stop base_other (empty_run b L R)

def cursor : Bool → List Bool → List Bool → Bool × List Bool
  | b,L,[] => (b,L)
  | b,L,x::xs => cursor x (b::L) xs

theorem cursor_contents (b : Bool) (L xs : List Bool) :
    (cursor b L xs).1 :: (cursor b L xs).2 = xs.reverse ++ b::L := by
  induction xs generalizing b L with
  | nil => rfl
  | cons x xs ih => simpa [cursor,List.reverse_cons,List.append_assoc] using ih x (b::L)

def cost : List Bool → Nat
  | [] => 4
  | _::xs => 20*xs.length+21+cost xs

def padding : Nat → List Bool → List Bool
  | 0,R => R
  | n+1,R => padding n (false::false::R)

/-- The same 43-row table converts every finite tagged buffer to raw bits,
in their original order, and reaches the empty continuation. -/
theorem run_all (xs L R : List Bool) (b : Bool) :
    run program (0,tapeAt L (b::false::tagged xs ++ false::R)) (cost xs) =
      some (.inr (12,tapeAt (cursor b L xs).2
        ((cursor b L xs).1::false::false::padding xs.length R))) := by
  induction xs generalizing b L R with
  | nil => simpa [cost,cursor,padding,Shared.Codes.FiniteProgramBitShuttle.tagged] using finish b L R
  | cons x xs ih =>
    simp only [cost]
    rw [run_continue _ _ _ _ _ (cycle b x xs L R)]
    simpa [cursor,padding,List.cons_append] using ih (b::L) (false::false::R) x

/-- Explicit quadratic bound in the number of tagged bits. -/
theorem cost_bound (xs : List Bool) : cost xs ≤ xs.length*(20*xs.length+21)+4 := by
  induction xs with
  | nil => simp [cost]
  | cons x xs ih =>
    let n := xs.length
    let bound := 20*(n+1)+21
    have hlocal : 20*n+21 ≤ bound := by dsimp [bound]; omega
    have hrec : cost xs ≤ n*bound+4 := by
      apply le_trans ih
      have hm : 20*n+21 ≤ bound := hlocal
      exact Nat.add_le_add_right (Nat.mul_le_mul_left n hm) 4
    change 20*n+21+cost xs ≤ (n+1)*bound+4
    calc
      _ ≤ bound+(n*bound+4) := Nat.add_le_add hlocal hrec
      _ = (n+1)*bound+4 := by simp [Nat.add_mul]; omega

/-- The first raw bit is extracted when there is no separator before the
tagged buffer. State 7 is the empty continuation; state 8 enters one shift. -/
def startPre : Program :=
  [ ((false,true,1,0),(true,true,1,0)),
    ((false,false,7,0),(true,true,2,0)),
    ((false,false,3,0),(true,false,4,0)),
    ((false,true,5,0),(false,true,5,0)),
    ((true,true,5,0),(true,true,5,0)),
    ((false,true,6,0),(true,true,6,0)),
    ((false,false,8,0),(false,false,8,0)),
    dummy ]

def startBase : Program := link startPre Shared.Codes.FiniteProgramDropTag.phase []

theorem startBase_length : startBase.length = 23 := by
  simp [startBase,link,startPre,Shared.Codes.FiniteProgramDropTag.phase,
    Shared.Codes.FiniteProgramTaggedAdvance.program]

theorem startBase_valid : valid startBase = true := by decide

theorem start_prepare (b x : Bool) (xs L R : List Bool) :
    run startBase (0,tapeAt L (b::tagged (x::xs) ++ false::R)) 6 =
      some (.inr (8,tapeAt (x::b::L) (x::false::tagged xs ++ false::R))) := by
  cases b <;> cases x <;> simp [startBase,link,startPre,run,advance,step,tagged_cons,tapeAt,moveTape]

theorem start_empty (b : Bool) (L R : List Bool) :
    run startBase (0,tapeAt L (b::false::R)) 2 = some (.inr (7,tapeAt L (b::false::R))) := by
  cases b <;> simp [startBase,link,startPre,run,advance,step,tapeAt,moveTape]

theorem start_base_cycle (b x : Bool) (xs L R : List Bool) :
    run startBase (0,tapeAt L (b::tagged (x::xs) ++ false::R)) (10*xs.length+11) =
      some (.inr (22,tapeAt (b::L) (x::false::tagged xs ++ false::false::R))) := by
  rw [show 10*xs.length+11 = 6+(10*xs.length+5) by omega]
  rw [run_continue _ _ _ _ _ (start_prepare b x xs L R)]
  have h := run_shift startPre Shared.Codes.FiniteProgramDropTag.phase []
    Shared.Codes.FiniteProgramDropTag.phase_valid
    (0,tapeAt (x::b::L) (x::false::tagged xs ++ false::R))
    (by simp [Shared.Codes.FiniteProgramDropTag.phase,Shared.Codes.FiniteProgramTaggedAdvance.program])
    (10*xs.length+5)
  have ha := Shared.Codes.FiniteProgramTaggedAdvance.advance [Shared.Codes.FiniteProgramDropTag.dummy]
    x x xs (b::L) R
  change run Shared.Codes.FiniteProgramDropTag.phase _ _ = _ at ha
  rw [ha] at h
  simpa [startBase,startPre,shiftConfig,shiftStatus] using h

theorem startBase_stop (t : Tape) : step startBase (22,t) = some (.inl false) := by
  have h := Shared.Codes.FiniteProgramLink.step_shift startPre Shared.Codes.FiniteProgramDropTag.phase []
    (14,t) (by simp [Shared.Codes.FiniteProgramDropTag.phase,Shared.Codes.FiniteProgramTaggedAdvance.program])
  have hs := Shared.Codes.FiniteProgramDropTag.phase_stop t
  change step Shared.Codes.FiniteProgramDropTag.phase (14,t) = _ at hs
  rw [hs] at h
  simpa [startBase,startPre,shiftConfig,shiftStatus] using h

def startProgram : Program := Shared.Codes.FiniteProgramSplice.program startBase program

theorem startProgram_valid : valid startProgram = true :=
  Shared.Codes.FiniteProgramSplice.program_valid _ _ startBase_valid program_valid

theorem startProgram_length : startProgram.length = 65 := by
  simp [startProgram,Shared.Codes.FiniteProgramSplice.program,link,
    Shared.Codes.FiniteProgramSplice.stem_length,startBase_length,program_length]

/-- Empty input is detected by the same entry table in two transitions. -/
theorem startProgram_empty (b : Bool) (L R : List Bool) :
    run startProgram (0,tapeAt L (b::false::R)) 2 = some (.inr (7,tapeAt L (b::false::R))) := by
  apply Shared.Codes.FiniteProgramSplice.first_run startBase program startBase_valid _ _ _ false
    (by simp [startBase_length]) (by simpa [startBase_length] using startBase_stop)
  exact start_empty b L R

/-- From an unseparated tagged buffer, extract its first bit and then run the
fixed 43-row loop. The source cell and all raw bits remain on the tape. -/
theorem startProgram_nonempty (b x : Bool) (xs L R : List Bool) :
    run startProgram (0,tapeAt L (b::tagged (x::xs) ++ false::R))
      (10*xs.length+11+cost xs) =
      some (.inr (34,tapeAt (cursor x (b::L) xs).2
        ((cursor x (b::L) xs).1::false::false::padding xs.length (false::R)))) := by
  have hf := Shared.Codes.FiniteProgramSplice.first_run startBase program startBase_valid _ _ _ false
    (by simp [startBase_length]) (by simpa [startBase_length] using startBase_stop)
    (start_base_cycle b x xs L R)
  have hs := Shared.Codes.FiniteProgramSplice.second_run startBase program program_valid
    (0,tapeAt (b::L) (x::false::tagged xs ++ false::false::R))
    (by simp [program_length]) (cost xs)
  rw [run_all] at hs
  change run (Shared.Codes.FiniteProgramSplice.program startBase program) _ _ = _
  rw [run_continue _ _ _ _ _ hf]
  simpa [startProgram,startBase_length,shiftConfig,shiftStatus] using hs

/-- A reverse scan of the whole tagged buffer arrives at the source cell.
It uses the already proved three-transition-per-triple pass. -/
theorem rewind (xs L R : List Bool) (p : Bool) :
    run Shared.Codes.FiniteProgramDropTag.phase
      (11,Shared.ComplexityBridge.PairReverseWitness.tapeLeft ((tagged xs).reverse ++ false::p::L) (false::R))
      (3*xs.length+1) =
      some (.inr (14,tapeAt L (p::false::tagged xs ++ false::R))) := by
  change run (Shared.Codes.FiniteProgramTaggedAdvance.program [Shared.Codes.FiniteProgramDropTag.dummy]) _ _ = _
  rw [run_continue _ _ _ _ _ (Shared.Codes.FiniteProgramTaggedAdvance.backward
    [Shared.Codes.FiniteProgramDropTag.dummy] xs (p::L) (false::R))]
  simpa [Shared.Codes.FiniteProgramDropTag.phase,Shared.ComplexityBridge.PairReverseWitness.tapeLeft,tapeAt]
    using Shared.Codes.FiniteProgramTaggedAdvance.finish_backward
      [Shared.Codes.FiniteProgramDropTag.dummy] (p::L) (tagged xs ++ false::R)

def returnPhase : Program := [((false,true,1,0),(true,true,1,0)),dummy]

theorem returnPhase_valid : valid returnPhase = true := by decide

theorem returnPhase_stop (t : Tape) : step returnPhase (returnPhase.length-1,t) = some (.inl false) := by
  cases h : t.2.1 <;> simp [returnPhase,dummy,step,h]

theorem return_step (p : Bool) (L R : List Bool) :
    run returnPhase (0,tapeAt L (p::false::R)) 1 =
      some (.inr (1,tapeAt (p::L) (false::R))) := by
  cases p <;> simp [returnPhase,run,advance,step,tapeAt,moveTape]

def returnStart : Program := Shared.Codes.FiniteProgramSplice.program returnPhase startProgram

theorem returnStart_valid : valid returnStart = true :=
  Shared.Codes.FiniteProgramSplice.program_valid _ _ returnPhase_valid startProgram_valid

theorem returnStart_length : returnStart.length = 66 := by
  simp [returnStart,Shared.Codes.FiniteProgramSplice.program,link,
    Shared.Codes.FiniteProgramSplice.stem_length,returnPhase,startProgram_length]

theorem return_untag (p x : Bool) (xs L R : List Bool) :
    run returnStart (0,tapeAt L (p::false::tagged (x::xs) ++ false::R))
      (1+(10*xs.length+11+cost xs)) =
      some (.inr (35,tapeAt (cursor x (false::p::L) xs).2
        ((cursor x (false::p::L) xs).1::false::false::padding xs.length (false::R)))) := by
  have hf := Shared.Codes.FiniteProgramSplice.first_run returnPhase startProgram returnPhase_valid _ _ _ false
    (by simp [returnPhase]) returnPhase_stop (return_step p L (tagged (x::xs) ++ false::R))
  have hs := Shared.Codes.FiniteProgramSplice.second_run returnPhase startProgram startProgram_valid
    (0,tapeAt (p::L) (false::tagged (x::xs) ++ false::R))
    (by simp [startProgram_length]) (10*xs.length+11+cost xs)
  rw [startProgram_nonempty] at hs
  change run (Shared.Codes.FiniteProgramSplice.program returnPhase startProgram) _ _ = _
  simp only [List.cons_append]
  rw [run_continue _ _ _ _ _ hf]
  simpa [returnPhase,shiftConfig,shiftStatus,List.cons_append] using hs

theorem return_empty (p : Bool) (L R : List Bool) :
    run returnStart (0,tapeAt L (p::false::false::R)) 3 =
      some (.inr (8,tapeAt (p::L) (false::false::R))) := by
  have hf := Shared.Codes.FiniteProgramSplice.first_run returnPhase startProgram returnPhase_valid _ _ _ false
    (by simp [returnPhase]) returnPhase_stop (return_step p L (false::R))
  have hs := Shared.Codes.FiniteProgramSplice.second_run returnPhase startProgram startProgram_valid
    (0,tapeAt (p::L) (false::false::R)) (by simp [startProgram_length]) 2
  rw [startProgram_empty] at hs
  change run (Shared.Codes.FiniteProgramSplice.program returnPhase startProgram) _ _ = _
  rw [show 3 = 1+2 by decide,run_continue _ _ _ _ _ hf]
  simpa [returnPhase,shiftConfig,shiftStatus] using hs

def rewindProgram : Program :=
  Shared.Codes.FiniteProgramSplice.program Shared.Codes.FiniteProgramDropTag.phase returnStart

theorem rewindProgram_valid : valid rewindProgram = true :=
  Shared.Codes.FiniteProgramSplice.program_valid _ _
    Shared.Codes.FiniteProgramDropTag.phase_valid returnStart_valid

theorem rewindProgram_length : rewindProgram.length = 80 := by
  simp [rewindProgram,Shared.Codes.FiniteProgramSplice.program,link,
    Shared.Codes.FiniteProgramSplice.stem_length,Shared.Codes.FiniteProgramDropTag.phase,
    Shared.Codes.FiniteProgramTaggedAdvance.program,returnStart_length]

/-- Starting at the right end of a nonempty tagged buffer, rewind it and
convert every bit to raw form using one finite table. The caller supplies
state 11 and the stated boundary layout. -/
theorem rewind_untag (p x : Bool) (xs L R : List Bool) :
    run rewindProgram
      (11,Shared.ComplexityBridge.PairReverseWitness.tapeLeft
        ((tagged (x::xs)).reverse ++ false::p::L) (false::R))
      (3*(x::xs).length+1+(1+(10*xs.length+11+cost xs))) =
      some (.inr (49,tapeAt (cursor x (false::p::L) xs).2
        ((cursor x (false::p::L) xs).1::false::false::padding xs.length (false::R)))) := by
  have hf := Shared.Codes.FiniteProgramSplice.first_run Shared.Codes.FiniteProgramDropTag.phase
    returnStart Shared.Codes.FiniteProgramDropTag.phase_valid _ _ _ false
    (by simp [Shared.Codes.FiniteProgramDropTag.phase,Shared.Codes.FiniteProgramTaggedAdvance.program])
    (Shared.Codes.FiniteProgramDropTag.phase_stop) (rewind (x::xs) L R p)
  have hs := Shared.Codes.FiniteProgramSplice.second_run Shared.Codes.FiniteProgramDropTag.phase
    returnStart returnStart_valid (0,tapeAt L (p::false::tagged (x::xs) ++ false::R))
    (by simp [returnStart_length]) (1+(10*xs.length+11+cost xs))
  rw [return_untag] at hs
  change run (Shared.Codes.FiniteProgramSplice.program Shared.Codes.FiniteProgramDropTag.phase returnStart) _ _ = _
  rw [run_continue _ _ _ _ _ hf]
  simpa [rewindProgram,Shared.Codes.FiniteProgramDropTag.phase,
    Shared.Codes.FiniteProgramTaggedAdvance.program,shiftConfig,shiftStatus] using hs

/-- The zero-length case also reaches a live continuation without inventing
a data bit. -/
theorem rewind_empty (p : Bool) (L R : List Bool) :
    run rewindProgram
      (11,Shared.ComplexityBridge.PairReverseWitness.tapeLeft (false::p::L) (false::R)) 4 =
      some (.inr (22,tapeAt (p::L) (false::false::R))) := by
  have hf := Shared.Codes.FiniteProgramSplice.first_run Shared.Codes.FiniteProgramDropTag.phase
    returnStart Shared.Codes.FiniteProgramDropTag.phase_valid _ _ _ false
    (by simp [Shared.Codes.FiniteProgramDropTag.phase,Shared.Codes.FiniteProgramTaggedAdvance.program])
    (Shared.Codes.FiniteProgramDropTag.phase_stop) (rewind [] L R p)
  have hs := Shared.Codes.FiniteProgramSplice.second_run Shared.Codes.FiniteProgramDropTag.phase
    returnStart returnStart_valid (0,tapeAt L (p::false::false::R)) (by simp [returnStart_length]) 3
  rw [return_empty] at hs
  change run (Shared.Codes.FiniteProgramSplice.program Shared.Codes.FiniteProgramDropTag.phase returnStart) _ _ = _
  rw [show 4 = 1+3 by decide,run_continue _ _ _ _ _ (by simpa [Shared.Codes.FiniteProgramBitShuttle.tagged] using hf)]
  simpa [Shared.Codes.FiniteProgramDropTag.phase,Shared.Codes.FiniteProgramTaggedAdvance.program,
    shiftConfig,shiftStatus] using hs

theorem rewind_cost_bound (x : Bool) (xs : List Bool) :
    3*(x::xs).length+1+(1+(10*xs.length+11+cost xs)) ≤
      3*(xs.length+1)+1+(1+(10*xs.length+11+(xs.length*(20*xs.length+21)+4))) := by
  have h := cost_bound xs
  simp only [List.length_cons]
  omega

/-- The frame decoder's cursor describes exactly a right-end view of the
same tagged word buffer, including its two source-side false cells. -/
theorem frame_cursor_tape (words L R : List Bool) :
    tapeAt (Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) words).2
        ((Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) words).1::false::R) =
      Shared.ComplexityBridge.PairReverseWitness.tapeLeft
        ((tagged words).reverse ++ false::false::L) (false::R) := by
  have h := Shared.Codes.FiniteProgramCrossTag.cursor_contents false (false::L) words
  rw [← h]
  simp [tapeAt,Shared.ComplexityBridge.PairReverseWitness.tapeLeft]

/-- Conditional handoff from the decoder's right-end tape to the untagger.
The caller must still connect the two control states with charged rows. -/
theorem untag_frame_cursor (x : Bool) (xs L R : List Bool) :
    run rewindProgram
      (11,tapeAt (Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) (x::xs)).2
        ((Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) (x::xs)).1::false::R))
      (3*(x::xs).length+1+(1+(10*xs.length+11+cost xs))) =
      some (.inr (49,tapeAt (cursor x (false::false::L) xs).2
        ((cursor x (false::false::L) xs).1::false::false::padding xs.length (false::R)))) := by
  rw [frame_cursor_tape]
  exact rewind_untag false x xs L R

theorem untag_frame_cursor_empty (L R : List Bool) :
    run rewindProgram
      (11,tapeAt (Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) []).2
        ((Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) []).1::false::R)) 4 =
      some (.inr (22,tapeAt (false::L) (false::false::R))) := by
  rw [frame_cursor_tape]
  simpa [Shared.Codes.FiniteProgramBitShuttle.tagged] using rewind_empty false L R

namespace Fixtures
example : cost [true,false,true] = 127 := by decide
example : cost [] = 4 := rfl
example : program.length = 43 := program_length
example : valid program = true := program_valid
example : run base (0,tapeAt [] [false,false,false]) 4 =
    some (.inr (12,tapeAt [] [false,false,false])) := by decide
example : rewindProgram.length = 80 := rewindProgram_length
end Fixtures

end Shared.Codes.FiniteProgramUntag
