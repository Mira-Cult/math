import Shared.ComplexityBridge.PairReverseWitness

/-! A literal single-tape shuttle across a self-delimiting tagged buffer.
Each buffer bit is represented by `[true,bit,true]`; false boundary cells
are recognizable from either direction. -/
namespace Shared.Codes.FiniteProgramBitShuttle
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed consumed_cons)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)

/-- State 15 is an arbitrary continuation, not executed by the shuttle. -/
def program (tail : Program) : Program :=
  [ ((false,true,1,0),(true,true,2,0)),
    ((false,true,3,0),(true,true,0,1)),
    ((false,true,4,0),(true,true,0,1)),
    ((false,true,9,0),(true,true,5,0)),
    ((false,true,10,0),(true,true,6,0)),
    ((false,true,7,0),(true,true,7,0)),
    ((false,true,8,0),(true,true,8,0)),
    ((false,true,0,1),(true,true,3,0)),
    ((false,true,0,1),(true,true,4,0)),
    ((false,false,11,0),(false,false,11,0)),
    ((true,false,11,0),(true,false,11,0)),
    ((false,false,12,0),(true,true,0,1)),
    ((false,false,15,0),(true,false,13,0)),
    ((false,false,14,0),(true,false,14,0)),
    ((false,true,0,1),(true,false,12,0)) ] ++ tail

def tagged (xs : List Bool) : List Bool := xs.flatMap (fun b => [true,b,true])

theorem tagged_cons (b : Bool) (xs : List Bool) :
    tagged (b::xs) = true::b::true::tagged xs := rfl

theorem tagged_append (xs ys : List Bool) : tagged (xs++ys) = tagged xs ++ tagged ys := by
  simp [tagged,List.flatMap_append]

theorem tagged_length (xs : List Bool) : (tagged xs).length = 3*xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [tagged_cons,ih]; omega

def boundary (b : Bool) : Nat := if b then 2 else 1
def front (b : Bool) : Nat := if b then 4 else 3
def middle (b : Bool) : Nat := if b then 6 else 5
def third (b : Bool) : Nat := if b then 8 else 7
def writer (b : Bool) : Nat := if b then 10 else 9

theorem start_step (tail : Program) (b : Bool) (L R : List Bool) :
    run (program tail) (0,tapeAt L (b::R)) 1 =
      some (.inr (boundary b,tapeAt (b::L) R)) := by
  cases b <;> simp [run,advance,step,program,tapeAt,moveTape,boundary]

theorem boundary_step (tail : Program) (b : Bool) (L R : List Bool) :
    run (program tail) (boundary b,tapeAt L (false::R)) 1 =
      some (.inr (front b,tapeAt (false::L) R)) := by
  cases b <;> simp [run,advance,step,program,tapeAt,moveTape,boundary,front]

theorem front_step (tail : Program) (b : Bool) (L R : List Bool) :
    run (program tail) (front b,tapeAt L (true::R)) 1 =
      some (.inr (middle b,tapeAt (true::L) R)) := by
  cases b <;> simp [run,advance,step,program,tapeAt,moveTape,front,middle]

theorem middle_step (tail : Program) (b x : Bool) (L R : List Bool) :
    run (program tail) (middle b,tapeAt L (x::R)) 1 =
      some (.inr (third b,tapeAt (x::L) R)) := by
  cases b <;> cases x <;> simp [run,advance,step,program,tapeAt,moveTape,middle,third]

theorem third_step (tail : Program) (b : Bool) (L R : List Bool) :
    run (program tail) (third b,tapeAt L (true::R)) 1 =
      some (.inr (front b,tapeAt (true::L) R)) := by
  cases b <;> simp [run,advance,step,program,tapeAt,moveTape,third,front]

theorem forward (tail : Program) (b : Bool) (xs L R : List Bool) :
    run (program tail) (front b,tapeAt L (tagged xs ++ R)) (3*xs.length) =
      some (.inr (front b,tapeAt (consumed L (tagged xs)) R)) := by
  induction xs generalizing L with
  | nil => rfl
  | cons x xs ih =>
    simp only [tagged_cons,List.cons_append,List.length_cons]
    rw [show 3*(xs.length+1) = 1+(1+(1+3*xs.length)) by omega]
    rw [run_continue _ _ _ 1 _ (front_step tail b L _)]
    rw [run_continue _ _ _ 1 _ (middle_step tail b x (true::L) _)]
    rw [run_continue _ _ _ 1 _ (third_step tail b (x::true::L) _)]
    simpa only [consumed_cons] using ih (true::x::true::L)

theorem end_step (tail : Program) (b : Bool) (L R : List Bool) :
    run (program tail) (front b,tapeAt L (false::R)) 1 =
      some (.inr (writer b,tapeAt (false::L) R)) := by
  cases b <;> simp [run,advance,step,program,tapeAt,moveTape,front,writer]

theorem write_step (tail : Program) (b old : Bool) (L R : List Bool) :
    run (program tail) (writer b,tapeAt (false::L) (old::R)) 1 =
      some (.inr (11,tapeLeft (false::L) (b::R))) := by
  cases b <;> cases old <;> simp [run,advance,step,program,tapeAt,tapeLeft,moveTape,writer]

theorem enter_reverse (tail : Program) (L R : List Bool) :
    run (program tail) (11,tapeLeft (false::L) R) 1 =
      some (.inr (12,tapeLeft L (false::R))) := by
  simp [run,advance,step,program,tapeLeft,moveTape]

theorem reverse_head (tail : Program) (L R : List Bool) :
    run (program tail) (12,tapeLeft (true::L) R) 1 =
      some (.inr (13,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,tapeLeft,moveTape]

theorem reverse_data (tail : Program) (x : Bool) (L R : List Bool) :
    run (program tail) (13,tapeLeft (x::L) R) 1 =
      some (.inr (14,tapeLeft L (x::R))) := by
  cases x <;> simp [run,advance,step,program,tapeLeft,moveTape]

theorem reverse_end (tail : Program) (L R : List Bool) :
    run (program tail) (14,tapeLeft (true::L) R) 1 =
      some (.inr (12,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,tapeLeft,moveTape]

theorem backward (tail : Program) (xs L R : List Bool) :
    run (program tail) (12,tapeLeft ((tagged xs).reverse ++ false::L) R) (3*xs.length) =
      some (.inr (12,tapeLeft (false::L) (tagged xs ++ R))) := by
  induction xs using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [tagged_append,tagged_cons]
    simp only [tagged,List.flatMap_nil,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.cons_append]
    change run (program tail)
      (12,tapeLeft (true::x::true::((tagged xs).reverse ++ false::L)) R)
        (3*(xs++[x]).length) = _
    rw [show 3*(xs++[x]).length = 1+(1+(1+3*xs.length)) by simp; omega]
    rw [run_continue _ _ _ 1 _ (reverse_head tail _ R)]
    rw [run_continue _ _ _ 1 _ (reverse_data tail x _ (true::R))]
    rw [run_continue _ _ _ 1 _ (reverse_end tail _ (x::true::R))]
    simpa [tagged,List.append_assoc] using ih (true::x::true::R)

theorem return_step (tail : Program) (L R : List Bool) :
    run (program tail) (12,tapeLeft (false::L) R) 1 =
      some (.inr (15,tapeLeft L (false::R))) := by
  simp [run,advance,step,program,tapeLeft,moveTape]

/-- Copy the live source bit across a tagged buffer, overwrite the designated
target cell, and return to the source. The complete run takes exactly
`6 * xs.length + 6` transitions, independently of the bit values. -/
theorem shuttle (tail : Program) (b old : Bool) (xs L R : List Bool) :
    run (program tail)
      (0,tapeAt L (b::false::tagged xs ++ false::old::R)) (6*xs.length+6) =
      some (.inr (15,tapeAt L (b::false::tagged xs ++ false::b::R))) := by
  simp only [List.cons_append]
  rw [show 6*xs.length+6 = 1+(1+(3*xs.length+(1+(1+(1+(3*xs.length+1)))))) by omega]
  rw [run_continue _ _ _ 1 _ (start_step tail b L _)]
  rw [run_continue _ _ _ 1 _ (boundary_step tail b (b::L) _)]
  rw [run_continue _ _ _ _ _ (forward tail b xs (false::b::L) (false::old::R))]
  rw [run_continue _ _ _ 1 _ (end_step tail b (consumed (false::b::L) (tagged xs)) (old::R))]
  rw [run_continue _ _ _ 1 _ (write_step tail b old (consumed (false::b::L) (tagged xs)) R)]
  rw [run_continue _ _ _ 1 _ (enter_reverse tail (consumed (false::b::L) (tagged xs)) (b::R))]
  simp only [consumed]
  rw [run_continue _ _ _ _ _ (backward tail xs (b::L) (false::b::R))]
  rw [return_step]
  simp [tapeAt,tapeLeft]

theorem shuttle_time_in_tape_cells (xs : List Bool) :
    6*xs.length+6 = 2*(tagged xs).length+6 := by rw [tagged_length]; omega

/-- A nonempty continuation makes the shuttle's return destination valid;
the continuation rows themselves must satisfy the full table's bounds. -/
theorem valid_of_continuation (tail : Program) (hne : 0 < tail.length)
    (htail : ∀ row ∈ tail, validRow (15+tail.length) row.1 = true ∧
      validRow (15+tail.length) row.2 = true) : valid (program tail) = true := by
  have hlen : (program tail).length = 15+tail.length := by simp [program]; omega
  have ht : tail.all (fun rows => validRow (15+tail.length) rows.1 &&
      validRow (15+tail.length) rows.2) = true := by
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
example : run (program []) (0,([],true,[false,false,false])) 6 =
    some (.inr (15,([],true,[false,false,true]))) := by decide
example : run (program []) (0,([],false,[false,true,true,true,false,true])) 12 =
    some (.inr (15,([],false,[false,true,true,true,false,false]))) := by decide
example : run (program []) (0,([],true,[false,true,false,true,true,true,true,false,false])) 18 =
    some (.inr (15,([],true,[false,true,false,true,true,true,true,false,true]))) := by decide
example : valid (program [((false,true,0,1),(true,true,0,1))]) = true := by decide
example : run (program []) (0,([],false,[true,false])) 2 = some (.inl false) := by decide
end Fixtures

end Shared.Codes.FiniteProgramBitShuttle
