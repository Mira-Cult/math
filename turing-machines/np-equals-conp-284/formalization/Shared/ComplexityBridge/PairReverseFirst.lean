import Shared.ComplexityBridge.PairReverseWitness

/-! Restore the marked separator and scan the first component backwards to
its left blank boundary. The following serializer is a separate obligation. -/
namespace Shared.ComplexityBridge.PairReverseFirst
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairReverseWitness

/-- States 8-13 scan one six-bit block per input bit; state 14 is the
continuation at the blank immediately left of the original input. -/
def program (onStart : Row) (tail : Program) : Program :=
  PairReverseWitness.program (false,false,8,0)
    ([ ((false,false,9,0),(true,true,0,1)),
       ((false,true,14,0),(true,false,10,0)),
       ((false,false,11,0),(true,false,11,0)),
       ((false,true,0,1),(true,false,12,0)),
       ((false,true,0,1),(true,false,13,0)),
       ((false,true,0,1),(true,false,8,0)),
       (onStart,(true,true,0,1)) ] ++ tail)

def expanded (xs : List Bool) : List Bool :=
  xs.flatMap (fun b => [true,true,true,b,true,false])

theorem expanded_cons (b : Bool) (xs : List Bool) :
    expanded (b::xs) = [true,true,true,b,true,false] ++ expanded xs := rfl

theorem expanded_append (xs ys : List Bool) : expanded (xs++ys) = expanded xs ++ expanded ys := by
  simp [expanded,List.flatMap_append]

theorem payload_expanded (xs : List Bool) :
    delimiterPayload (BitstringEncoding.bitEncode xs) = expanded xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [encode_cons,expanded_cons]
    have he : delimiterPayload ([true,b,false] ++ BitstringEncoding.bitEncode xs) =
        [true,true,true,b,true,false] ++ delimiterPayload (BitstringEncoding.bitEncode xs) := by
      simp [delimiterPayload]
    rw [he,ih]

theorem markerLeft_eq (x : List Bool) : markerLeft x = (expanded x).reverse := by
  simp [markerLeft,payload_expanded]

theorem restore_separator (hit : Row) (tail : Program) (L R : List Bool) :
    run (program hit tail) (5,tapeLeft (true::L) R) 1 =
      some (.inr (8,tapeLeft L (false::R))) := by
  simp [run,advance,step,program,PairReverseWitness.program,
    PairMarkedScanner.program,tapeLeft,moveTape]

theorem first_zero (hit : Row) (tail : Program) (L R : List Bool) :
    run (program hit tail) (8,tapeLeft (false::L) R) 1 =
      some (.inr (9,tapeLeft L (false::R))) := by
  simp [run,advance,step,program,PairReverseWitness.program,
    PairMarkedScanner.program,tapeLeft,moveTape]

theorem first_one (hit : Row) (tail : Program) (L R : List Bool) :
    run (program hit tail) (9,tapeLeft (true::L) R) 1 =
      some (.inr (10,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,PairReverseWitness.program,
    PairMarkedScanner.program,tapeLeft,moveTape]

theorem first_data (hit : Row) (tail : Program) (L R : List Bool) (b : Bool) :
    run (program hit tail) (10,tapeLeft (b::L) R) 1 =
      some (.inr (11,tapeLeft L (b::R))) := by
  cases b <;> simp [run,advance,step,program,PairReverseWitness.program,
    PairMarkedScanner.program,tapeLeft,moveTape]

theorem first_one11 (hit : Row) (tail : Program) (L R : List Bool) :
    run (program hit tail) (11,tapeLeft (true::L) R) 1 =
      some (.inr (12,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,PairReverseWitness.program,
    PairMarkedScanner.program,tapeLeft,moveTape]

theorem first_one12 (hit : Row) (tail : Program) (L R : List Bool) :
    run (program hit tail) (12,tapeLeft (true::L) R) 1 =
      some (.inr (13,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,PairReverseWitness.program,
    PairMarkedScanner.program,tapeLeft,moveTape]

theorem first_one13 (hit : Row) (tail : Program) (L R : List Bool) :
    run (program hit tail) (13,tapeLeft (true::L) R) 1 =
      some (.inr (8,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,PairReverseWitness.program,
    PairMarkedScanner.program,tapeLeft,moveTape]

/-- Every first-component bit is traversed in exactly six moves. -/
theorem scan_reverse (hit : Row) (tail : Program) (xs L R : List Bool) :
    run (program hit tail) (8,tapeLeft ((expanded xs).reverse ++ L) R) (6*xs.length) =
      some (.inr (8,tapeLeft L (expanded xs ++ R))) := by
  induction xs using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton xs b ih =>
    rw [expanded_append,expanded_cons]
    simp only [expanded,List.flatMap_nil,List.append_nil,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.cons_append]
    change run (program hit tail)
      (8,tapeLeft (false::true::b::true::true::true::((expanded xs).reverse ++ L)) R)
        (6*(xs++[b]).length) = _
    rw [show 6*(xs++[b]).length = 1+(1+(1+(1+(1+(1+6*xs.length))))) by simp; omega]
    rw [run_continue _ _ _ 1 _ (first_zero hit tail _ R)]
    rw [run_continue _ _ _ 1 _ (first_one hit tail _ (false::R))]
    rw [run_continue _ _ _ 1 _ (first_data hit tail _ (true::false::R) b)]
    rw [run_continue _ _ _ 1 _ (first_one11 hit tail _ (b::true::false::R))]
    rw [run_continue _ _ _ 1 _ (first_one12 hit tail _ (true::b::true::false::R))]
    rw [run_continue _ _ _ 1 _ (first_one13 hit tail _ (true::true::b::true::false::R))]
    simpa [List.append_assoc,expanded] using ih (true::true::true::b::true::false::R)

/-- The extra blank probe distinguishes the start boundary from the next
six-bit block, then returns one position to the right. -/
theorem finish_blank (hit : Row) (tail : Program) (R : List Bool) :
    run (program hit tail) (8,tapeLeft [] R) 2 = some (.inr (14,([false],false,R))) := by
  simp [run,advance,step,program,PairReverseWitness.program,
    PairMarkedScanner.program,tapeLeft,moveTape]

theorem delimit_eq_payload (xs : List Bool) :
    BitstringEncoding.delimit xs = delimiterPayload xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [BitstringEncoding.delimit,delimiterPayload,ih]

theorem pair_encoding (x w : List Bool) :
    BitstringEncoding.bitEncode (x,w) = expanded x ++ false::BitstringEncoding.bitEncode w := by
  change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode w = _
  rw [delimit_eq_payload,payload_expanded]
  simp [List.append_assoc]

/-- The original pair is restored, and the head is on a blank immediately to
its left. The explicit extra false on the far right is a blank cell. -/
theorem restore_and_rewind (hit : Row) (tail : Program) (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    run (program hit tail) (initial input) (input.length+1+3*w.length+1+6*x.length+2) =
      some (.inr (14,([false],false,input ++ [false]))) := by
  let rest : Program :=
    [ ((false,false,9,0),(true,true,0,1)),
      ((false,true,14,0),(true,false,10,0)),
      ((false,false,11,0),(true,false,11,0)),
      ((false,true,0,1),(true,false,12,0)),
      ((false,true,0,1),(true,false,13,0)),
      ((false,true,0,1),(true,false,8,0)),
      (hit,(true,true,0,1)) ] ++ tail
  have hf := forward_then_reverse (false,false,8,0) rest x w
  change run (program hit tail) (initial (BitstringEncoding.bitEncode (x,w)))
    ((BitstringEncoding.bitEncode (x,w)).length+1+3*w.length) =
      some (.inr (5,tapeLeft (true::markerLeft x) (BitstringEncoding.bitEncode w ++ [false]))) at hf
  dsimp only
  rw [show (BitstringEncoding.bitEncode (x,w)).length+1+3*w.length+1+6*x.length+2 =
      ((BitstringEncoding.bitEncode (x,w)).length+1+3*w.length) + (1+(6*x.length+2)) by omega]
  rw [run_continue _ _ _ _ _ hf]
  rw [run_continue _ _ _ 1 _ (restore_separator hit tail (markerLeft x) (BitstringEncoding.bitEncode w ++ [false]))]
  rw [markerLeft_eq]
  have hscan := scan_reverse hit tail x [] (false::(BitstringEncoding.bitEncode w ++ [false]))
  simp only [List.append_nil] at hscan
  rw [run_continue _ _ _ _ _ hscan,finish_blank]
  simp [pair_encoding,List.append_assoc]

/-- The full scan and rewind have a linear exact cost in both raw lengths. -/
theorem restore_and_rewind_time (x w : List Bool) :
    (BitstringEncoding.bitEncode (x,w)).length+1+3*w.length+1+6*x.length+2 =
      12*x.length+6*w.length+5 := by
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
  omega

/-- The final dispatch and appended continuation must be valid in the full
15-state prefix plus continuation table. -/
theorem valid_of_continuation (hit : Row) (tail : Program)
    (hstart : validRow (15+tail.length) hit = true)
    (htail : ∀ row ∈ tail, validRow (15+tail.length) row.1 = true ∧
      validRow (15+tail.length) row.2 = true) : valid (program hit tail) = true := by
  have hlen : (program hit tail).length = 15+tail.length := by
    simp [program,PairReverseWitness.program,PairMarkedScanner.program]
    omega
  have ht : tail.all (fun rows => validRow (15+tail.length) rows.1 &&
      validRow (15+tail.length) rows.2) = true := by
    rw [List.all_eq_true]
    intro rows hrows
    obtain ⟨h₁,h₂⟩ := htail rows hrows
    simp [h₁,h₂]
  unfold valid
  rw [hlen]
  simp only [program,PairReverseWitness.program,PairMarkedScanner.program,List.cons_append,List.nil_append,
    List.isEmpty_cons,Bool.not_false,Bool.true_and,List.all_cons,hstart,ht,Bool.and_true]
  simp [validRow]
  omega

namespace Fixtures
example : run (program (false,false,0,1) []) (initial [false]) 5 =
    some (.inr (14,([false],false,[false,false]))) := by decide
example : valid (program (false,false,0,1) []) = true := by decide
example : run (program (false,false,0,1) [])
    (initial (BitstringEncoding.bitEncode (([false] : List Bool),[true]))) 23 =
      some (.inr (14,([false],false,BitstringEncoding.bitEncode (([false] : List Bool),[true]) ++ [false]))) := by decide
end Fixtures

end Shared.ComplexityBridge.PairReverseFirst
