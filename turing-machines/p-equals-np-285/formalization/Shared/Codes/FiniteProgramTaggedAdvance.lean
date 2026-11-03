import Shared.Codes.FiniteProgramBitShuttle

/-! Shift a tagged buffer one cell left, erase the consumed source bit, and
move to its left neighbor. This preserves the separator/buffer invariant for
the next source bit. -/
namespace Shared.Codes.FiniteProgramTaggedAdvance
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons tagged_append)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)

/-- State 14 is supplied by the caller and is not executed by this pass. -/
def program (tail : Program) : Program :=
  [ ((false,true,1,0),(false,true,1,0)),
    ((false,true,2,0),(true,true,0,1)),
    ((false,false,10,0),(true,true,3,0)),
    ((false,false,4,0),(true,false,5,0)),
    ((false,false,6,0),(false,false,6,0)),
    ((true,false,6,0),(true,false,6,0)),
    ((true,true,7,0),(true,true,7,0)),
    ((false,true,8,0),(true,true,8,0)),
    ((true,true,9,0),(true,true,9,0)),
    ((false,true,0,1),(true,true,2,0)),
    ((false,false,11,0),(false,false,11,0)),
    ((false,false,14,0),(true,false,12,0)),
    ((false,false,13,0),(true,false,13,0)),
    ((false,true,0,1),(true,false,11,0)) ] ++ tail

def outputLeft (xs : List Bool) (free : Bool) (L : List Bool) : List Bool :=
  (if xs.isEmpty then free else true) :: (tagged xs).reverse ++ L

theorem outputLeft_cons (x : Bool) (xs : List Bool) (free : Bool) (L : List Bool) :
    outputLeft (x::xs) free L = outputLeft xs true (true::x::true::L) := by
  cases xs <;> simp [outputLeft,tagged_cons,List.reverse_cons,List.append_assoc]

theorem start_step (tail : Program) (b p : Bool) (L R : List Bool) :
    run (program tail) (0,tapeAt (p::L) (b::false::R)) 2 =
      some (.inr (2,tapeAt (false::false::p::L) R)) := by
  cases b <;> simp [run,advance,step,program,tapeAt,moveTape]

/-- Shift one tagged block into the preceding cell in seven transitions. -/
theorem block_step (tail : Program) (free x : Bool) (L R : List Bool) :
    run (program tail) (2,tapeAt (free::L) (true::x::true::R)) 7 =
      some (.inr (2,tapeAt (true::true::x::true::L) R)) := by
  cases free <;> cases x <;> simp [run,advance,step,program,tapeAt,moveTape]

theorem forward (tail : Program) (xs : List Bool) (free : Bool) (L R : List Bool) :
    run (program tail) (2,tapeAt (free::L) (tagged xs ++ false::R)) (7*xs.length) =
      some (.inr (2,tapeAt (outputLeft xs free L) (false::R))) := by
  induction xs generalizing free L with
  | nil => simp [outputLeft,tagged]
  | cons x xs ih =>
    simp only [tagged_cons,List.cons_append,List.length_cons]
    rw [show 7*(xs.length+1) = 7+7*xs.length by omega]
    rw [run_continue _ _ _ 7 _ (block_step tail free x L _)]
    rw [outputLeft_cons]
    exact ih true (true::x::true::L)

theorem finish_forward (tail : Program) (free : Bool) (L R : List Bool) :
    run (program tail) (2,tapeAt (free::L) (false::R)) 2 =
      some (.inr (11,tapeLeft L (false::false::R))) := by
  cases free <;> simp [run,advance,step,program,tapeAt,tapeLeft,moveTape]

theorem reverse_head (tail : Program) (L R : List Bool) :
    run (program tail) (11,tapeLeft (true::L) R) 1 =
      some (.inr (12,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,tapeLeft,moveTape]

theorem reverse_data (tail : Program) (b : Bool) (L R : List Bool) :
    run (program tail) (12,tapeLeft (b::L) R) 1 =
      some (.inr (13,tapeLeft L (b::R))) := by
  cases b <;> simp [run,advance,step,program,tapeLeft,moveTape]

theorem reverse_end (tail : Program) (L R : List Bool) :
    run (program tail) (13,tapeLeft (true::L) R) 1 =
      some (.inr (11,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,tapeLeft,moveTape]

theorem backward (tail : Program) (xs L R : List Bool) :
    run (program tail) (11,tapeLeft ((tagged xs).reverse ++ false::L) R) (3*xs.length) =
      some (.inr (11,tapeLeft (false::L) (tagged xs ++ R))) := by
  induction xs using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton xs b ih =>
    rw [tagged_append,tagged_cons]
    simp only [tagged,List.flatMap_nil,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.cons_append]
    change run (program tail) (11,tapeLeft (true::b::true::((tagged xs).reverse ++ false::L)) R)
      (3*(xs++[b]).length) = _
    rw [show 3*(xs++[b]).length = 1+(1+(1+3*xs.length)) by simp; omega]
    rw [run_continue _ _ _ 1 _ (reverse_head tail _ R)]
    rw [run_continue _ _ _ 1 _ (reverse_data tail b _ (true::R))]
    rw [run_continue _ _ _ 1 _ (reverse_end tail _ (b::true::R))]
    simpa [tagged,List.append_assoc] using ih (true::b::true::R)

theorem finish_backward (tail : Program) (L R : List Bool) :
    run (program tail) (11,tapeLeft (false::L) R) 1 =
      some (.inr (14,tapeLeft L (false::R))) := by
  simp [run,advance,step,program,tapeLeft,moveTape]

/-- Erase the consumed bit, shift the buffer, and return at its predecessor.
The next input bit `p` must already exist immediately to the left. -/
theorem advance (tail : Program) (b p : Bool) (xs L R : List Bool) :
    run (program tail) (0,tapeAt (p::L) (b::false::tagged xs ++ false::R)) (10*xs.length+5) =
      some (.inr (14,tapeAt L (p::false::tagged xs ++ false::false::R))) := by
  simp only [List.cons_append]
  rw [show 10*xs.length+5 = 2+(7*xs.length+(2+(3*xs.length+1))) by omega]
  rw [run_continue _ _ _ 2 _ (start_step tail b p L _)]
  rw [run_continue _ _ _ _ _ (forward tail xs false (false::p::L) R)]
  simp only [outputLeft,List.cons_append]
  rw [run_continue _ _ _ 2 _ (finish_forward tail (if xs.isEmpty then false else true)
    ((tagged xs).reverse ++ false::p::L) R)]
  rw [run_continue _ _ _ _ _ (backward tail xs (p::L) (false::false::R))]
  rw [finish_backward]
  simp [tapeAt,tapeLeft]

theorem valid_of_continuation (tail : Program) (hne : 0 < tail.length)
    (htail : ∀ row ∈ tail, validRow (14+tail.length) row.1 = true ∧
      validRow (14+tail.length) row.2 = true) : valid (program tail) = true := by
  have hlen : (program tail).length = 14+tail.length := by simp [program]; omega
  have ht : tail.all (fun rows => validRow (14+tail.length) rows.1 &&
      validRow (14+tail.length) rows.2) = true := by
    rw [List.all_eq_true]
    intro rows hrows
    obtain ⟨h₁,h₂⟩ := htail rows hrows
    simp [h₁,h₂]
  unfold valid
  rw [hlen]
  simp only [program,List.cons_append,List.nil_append,List.isEmpty_cons,Bool.not_false,
    Bool.true_and,List.all_cons,ht,Bool.and_true]
  simp [validRow]
  omega

namespace Fixtures
example : run (program []) (0,tapeAt [true] [false,false,false]) 5 =
    some (.inr (14,tapeAt [] [true,false,false,false])) := by decide
example : run (program []) (0,tapeAt [false] [true,false,true,false,true,false]) 15 =
    some (.inr (14,tapeAt [] [false,false,true,false,true,false,false])) := by decide
example : valid (program [((false,true,0,1),(true,true,0,1))]) = true := by decide
end Fixtures

end Shared.Codes.FiniteProgramTaggedAdvance
