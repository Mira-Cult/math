import Shared.Codes.FiniteProgramTaggedAdvance
import Shared.Codes.FiniteProgramSplice
import Shared.ComplexityBridge.FirstBlocksContent

/-! Remove the first tagged datum by three concrete buffer shifts. The
remaining data stay tagged; decoding words to raw bits is a separate task. -/
namespace Shared.Codes.FiniteProgramDropTag
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons)
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramSplice (stem)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)


def dummy : Row × Row := ((false,true,0,1),(true,true,0,1))
def phase : Program := Shared.Codes.FiniteProgramTaggedAdvance.program [dummy]

theorem phase_valid : valid phase = true := by decide

theorem phase_stop (t : Tape) : step phase (phase.length-1,t) = some (.inl false) := by
  cases h : t.2.1 <;> simp [phase,Shared.Codes.FiniteProgramTaggedAdvance.program,dummy,step,h]

def phases : Nat → Program
  | 0 => [dummy]
  | n+1 => Shared.Codes.FiniteProgramSplice.program phase (phases n)

theorem phases_valid (n : Nat) : valid (phases n) = true := by
  induction n with
  | zero => decide
  | succ n ih => exact Shared.Codes.FiniteProgramSplice.program_valid phase _ phase_valid ih

theorem phases_length (n : Nat) : (phases n).length = 14*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [phases,Shared.Codes.FiniteProgramSplice.program,link,
      Shared.Codes.FiniteProgramSplice.stem_length,phase,Shared.Codes.FiniteProgramTaggedAdvance.program,ih]
    omega

theorem first_phase (n : Nat) (b p : Bool) (xs L R : List Bool) :
    run (phases (n+1)) (0,tapeAt (p::L) (b::false::tagged xs ++ false::R))
      (10*xs.length+5) =
      some (.inr (14,tapeAt L (p::false::tagged xs ++ false::false::R))) := by
  have h := Shared.Codes.FiniteProgramTaggedAdvance.advance [dummy] b p xs L R
  have h' := Shared.Codes.FiniteProgramSplice.first_run phase (phases n) phase_valid
    _ _ _ false (by simp [phase,Shared.Codes.FiniteProgramTaggedAdvance.program]) phase_stop h
  simpa [phases,phase,Shared.Codes.FiniteProgramTaggedAdvance.program] using h'

theorem rest_phase (n : Nat) (c : Config) (hc : c.1 < (phases n).length) (k : Nat) :
    run (phases (n+1)) (shiftConfig 14 c) k = shiftStatus 14 (run (phases n) c k) := by
  have h := Shared.Codes.FiniteProgramSplice.second_run phase (phases n) (phases_valid n) c hc k
  simpa [phases,phase,Shared.Codes.FiniteProgramTaggedAdvance.program] using h

/-- Three advances remove three cells between the current source and the
surviving tagged buffer. They charge all three physical scans. -/
theorem three_phases (b m : Bool) (xs L R : List Bool) :
    run (phases 3) (0,tapeAt (true::false::b::L) (m::false::tagged xs ++ false::R))
      (3*(10*xs.length+5)) =
      some (.inr (42,tapeAt L (b::false::tagged xs ++ false::false::false::false::R))) := by
  let c := 10*xs.length+5
  have h1 := first_phase 2 m true xs (false::b::L) R
  have h2 := first_phase 1 true false xs (b::L) (false::R)
  have h3 := first_phase 0 false b xs L (false::false::R)
  have hc2 : (0,tapeAt (false::b::L) (true::false::tagged xs ++ false::false::R)).1 < (phases 2).length := by
    simp [phases_length]
  have hc3 : (0,tapeAt (b::L) (false::false::tagged xs ++ false::false::false::R)).1 < (phases 1).length := by
    simp [phases_length]
  have htail : run (phases 2) (0,tapeAt (false::b::L) (true::false::tagged xs ++ false::false::R)) (2*c) =
      some (.inr (28,tapeAt L (b::false::tagged xs ++ false::false::false::false::R))) := by
    rw [show 2*c = c+c by omega,run_continue _ _ _ _ _ h2]
    have hr := rest_phase 1 _ hc3 c
    simpa [shiftConfig,shiftStatus,c] using hr.trans (by rw [h3]; rfl)
  rw [show 3*(10*xs.length+5) = c+2*c by simp [c]; omega,run_continue _ _ _ _ _ h1]
  have hr := rest_phase 2 _ hc2 (2*c)
  simpa [shiftConfig,shiftStatus,c] using hr.trans (by rw [htail]; rfl)

/-- Five rows expose the final cell of the metadata triple as a separator.
The following three phases remove the triple. -/
def setup : Program :=
  [ ((false,true,1,0),(true,true,1,0)),
    ((false,true,2,0),(true,true,2,0)),
    ((false,true,3,0),(true,true,3,0)),
    ((false,true,4,0),(true,true,4,0)),
    ((false,false,5,0),(false,false,5,0)) ]

def program : Program := link setup (phases 3) []

theorem program_length : program.length = 48 := by simp [program,link,setup,phases_length]

theorem program_valid : valid program = true := by decide

theorem setup_run (b m : Bool) (xs L R : List Bool) :
    run program (0,tapeAt L (b::false::tagged (m::xs) ++ false::R)) 5 =
      some (.inr (5,tapeAt (true::false::b::L) (m::false::tagged xs ++ false::R))) := by
  cases b <;> cases m <;>
    simp [program,link,setup,run,advance,step,tagged_cons,tapeAt,moveTape]

/-- For any tagged suffix, delete its preceding metadata block. The result
is still tagged. State 47 is an unexecuted terminal continuation; all 48
rows form a valid table. The exact cost is in primitive tape transitions. -/
theorem drop_first (b m : Bool) (xs L R : List Bool) :
    run program (0,tapeAt L (b::false::tagged (m::xs) ++ false::R))
      (30*xs.length+20) =
      some (.inr (47,tapeAt L (b::false::tagged xs ++ false::false::false::false::R))) := by
  rw [show 30*xs.length+20 = 5+3*(10*xs.length+5) by omega]
  rw [run_continue _ _ _ _ _ (setup_run b m xs L R)]
  have h := run_shift setup (phases 3) [] (phases_valid 3)
    (0,tapeAt (true::false::b::L) (m::false::tagged xs ++ false::R))
    (by simp [phases_length]) (3*(10*xs.length+5))
  rw [three_phases] at h
  simpa [program,setup,shiftConfig,shiftStatus] using h

open Shared.ComplexityBridge.FirstBlocksContent (frames frames_cons selected selected_length)

theorem frames_length (zero one bits : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) :
    (frames zero one bits).length = bits.length * (width+1) := by
  induction bits with
  | nil => simp [Shared.ComplexityBridge.FirstBlocksContent.frames]
  | cons b bits ih =>
    rw [frames_cons]
    simp only [List.length_append,List.length_cons,ih,
      selected_length zero one width hzero hone b, Nat.succ_mul]
    omega

/-- Drop the first metadata datum from a complete framed buffer. The first
selected word remains tagged, as do all later frames. -/
theorem drop_first_frame (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (head m : Bool) (bits L R : List Bool) :
    run program (0,tapeAt L (head::false::tagged (frames zero one (m::bits)) ++ false::R))
      (30*(width+bits.length*(width+1))+20) =
      some (.inr (47,tapeAt L (head::false::tagged (selected zero one m ++ frames zero one bits) ++
        false::false::false::false::R))) := by
  have h := drop_first head m (selected zero one m ++ frames zero one bits) L R
  simpa [frames_cons,selected_length zero one width hzero hone m,
    frames_length zero one bits width hzero hone] using h

/-- Specialization to the pinned TM2 translated input-cell words. -/
theorem drop_first_tm2 (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (head m : Bool) (bits L R : List Bool) :
    let zero := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let one := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    run program (0,tapeAt L (head::false::tagged (frames zero one (m::bits)) ++ false::R))
      (30*(width+bits.length*(width+1))+20) =
      some (.inr (47,tapeAt L (head::false::tagged (selected zero one m ++ frames zero one bits) ++
        false::false::false::false::R))) := by
  exact drop_first_frame _ _ width
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true) head m bits L R

namespace Fixtures
example : program.length = 48 := by decide
example : valid program = true := by decide
example : run program (0,tapeAt [] [true,false,true,false,true,false]) 20 =
    some (.inr (47,tapeAt [] [true,false,false,false,false,false])) := by decide
example : run program (0,tapeAt [] [false,false,true,true,true,true,false,true,false]) 50 =
    some (.inr (47,tapeAt [] [false,false,true,false,true,false,false,false,false])) := by decide
end Fixtures

end Shared.Codes.FiniteProgramDropTag
