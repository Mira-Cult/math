import Shared.ComplexityBridge.PairMarkedScanner

/-! The second stage of the binary input wrapper: scan the witness backward
to the marked first-component delimiter. This is not the complete serializer. -/
namespace Shared.ComplexityBridge.PairReverseWitness
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner

/-- States 5-7 traverse each reversed witness block. `onMarker` is the row
for the marked delimiter and is not executed by the reverse scan itself. -/
def program (onMarker : Row) (tail : Program) : Program :=
  PairMarkedScanner.program (false,false,5,0)
    ([ ((false,false,6,0),onMarker),
       ((false,false,7,0),(true,false,7,0)),
       ((false,false,5,0),(true,false,5,0)) ] ++ tail)

/-- The first component includes the current head cell. -/
def tapeLeft (left right : List Bool) : Tape := (left.tail,left.head?.getD false,right)

theorem reverse_marker (hit : Row) (tail : Program) (L R : List Bool) :
    run (program hit tail) (5,tapeLeft (false::L) R) 1 =
      some (.inr (6,tapeLeft L (false::R))) := by
  simp [run,advance,step,program,PairMarkedScanner.program,tapeLeft,moveTape]

theorem reverse_data (hit : Row) (tail : Program) (L R : List Bool) (b : Bool) :
    run (program hit tail) (6,tapeLeft (b::L) R) 1 =
      some (.inr (7,tapeLeft L (b::R))) := by
  cases b <;> simp [run,advance,step,program,PairMarkedScanner.program,tapeLeft,moveTape]

theorem reverse_end (hit : Row) (tail : Program) (L R : List Bool) :
    run (program hit tail) (7,tapeLeft (true::L) R) 1 =
      some (.inr (5,tapeLeft L (true::R))) := by
  simp [run,advance,step,program,PairMarkedScanner.program,tapeLeft,moveTape]

theorem encode_cons (b : Bool) (xs : List Bool) :
    BitstringEncoding.bitEncode (b::xs) = [true,b,false] ++ BitstringEncoding.bitEncode xs := by rfl

theorem encode_append (xs ys : List Bool) :
    BitstringEncoding.bitEncode (xs++ys) = BitstringEncoding.bitEncode xs ++ BitstringEncoding.bitEncode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [List.cons_append,encode_cons,encode_cons,ih,List.append_assoc]

/-- Each reversed witness bit costs exactly three target transitions. The
right side of the tape retains the witness in its original encoded order. -/
theorem scan_reverse (hit : Row) (tail : Program) (ws L R : List Bool) :
    run (program hit tail)
      (5,tapeLeft ((BitstringEncoding.bitEncode ws).reverse ++ true::L) R) (3*ws.length) =
      some (.inr (5,tapeLeft (true::L) (BitstringEncoding.bitEncode ws ++ R))) := by
  induction ws using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton ws b ih =>
    rw [encode_append,encode_cons]
    have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
    simp only [hnil,List.append_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
    change run (program hit tail)
      (5,tapeLeft (false::b::true::((BitstringEncoding.bitEncode ws).reverse ++ true::L)) R)
        (3*(ws++[b]).length) = _
    rw [show 3*(ws++[b]).length = 1+(1+(1+3*ws.length)) by simp; omega]
    rw [run_continue _ _ _ 1 _ (reverse_marker hit tail _ R)]
    rw [run_continue _ _ _ 1 _ (reverse_data hit tail _ (false::R) b)]
    rw [run_continue _ _ _ 1 _ (reverse_end hit tail _ (b::false::R))]
    simpa [List.append_assoc] using ih (true::b::false::R)

/-- Delimiter payload before the terminal marker. -/
def delimiterPayload (xs : List Bool) : List Bool := xs.flatMap (fun b => [true,b])

theorem markedDelimit_eq (xs : List Bool) : markedDelimit xs = delimiterPayload xs ++ [true] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [markedDelimit,delimiterPayload,ih]

def markerLeft (x : List Bool) : List Bool := (delimiterPayload (BitstringEncoding.bitEncode x)).reverse

theorem markedPair_reverse (x w : List Bool) :
    (markedPair x w).reverse = (BitstringEncoding.bitEncode w).reverse ++ true::markerLeft x := by
  simp [markedPair,markedDelimit_eq,markerLeft,List.reverse_append]

/-- Starting on the canonical input, scan forward, mark the delimiter, and
return over the complete witness. The head then reads the marked delimiter;
the witness is preserved on its right. -/
theorem forward_then_reverse (hit : Row) (tail : Program) (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    run (program hit tail) (initial input) (input.length+1+3*w.length) =
      some (.inr (5,tapeLeft (true::markerLeft x) (BitstringEncoding.bitEncode w ++ [false]))) := by
  let rest : Program :=
    [ ((false,false,6,0),hit),
      ((false,false,7,0),(true,false,7,0)),
      ((false,false,5,0),(true,false,5,0)) ] ++ tail
  have hf := scan_and_enter_reverse 5 rest x w
  change run (program hit tail) (initial (BitstringEncoding.bitEncode (x,w)))
    ((BitstringEncoding.bitEncode (x,w)).length+1) =
    some (.inr (5,moveTape true false (tapeAt (consumed [] (markedPair x w)) []))) at hf
  dsimp only
  rw [run_continue _ _ _ _ _ hf]
  have ht : moveTape true false (tapeAt (consumed [] (markedPair x w)) []) =
      tapeLeft ((BitstringEncoding.bitEncode w).reverse ++ true::markerLeft x) [false] := by
    simp [tapeAt,consumed,markedPair_reverse,moveTape,tapeLeft]
  rw [ht,scan_reverse]

/-- Both scans together use exactly this many finite-program transitions. -/
theorem forward_then_reverse_time (x w : List Bool) :
    (BitstringEncoding.bitEncode (x,w)).length+1+3*w.length = 6*x.length+6*w.length+2 := by
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
  omega

/-- The continuation can be appended while preserving table validity, as
long as its rows and the marker dispatch target are valid in the full table. -/
theorem valid_of_continuation (hit : Row) (tail : Program)
    (hmarker : validRow (8+tail.length) hit = true)
    (htail : ∀ row ∈ tail, validRow (8+tail.length) row.1 = true ∧
      validRow (8+tail.length) row.2 = true) : valid (program hit tail) = true := by
  have hlen : (program hit tail).length = 8+tail.length := by
    simp [program,PairMarkedScanner.program]
    omega
  have ht : tail.all (fun rows => validRow (8+tail.length) rows.1 &&
      validRow (8+tail.length) rows.2) = true := by
    rw [List.all_eq_true]
    intro rows hrows
    obtain ⟨h₁,h₂⟩ := htail rows hrows
    simp [h₁,h₂]
  unfold valid
  rw [hlen]
  simp only [program,PairMarkedScanner.program,List.cons_append,List.nil_append,List.isEmpty_cons,
    Bool.not_false,Bool.true_and,List.all_cons,Prod.fst,Prod.snd,hmarker,ht,Bool.and_true]
  simp [validRow]
  omega

namespace Fixtures
example : markerLeft [] = [] := rfl
example : run (program (false,false,0,1) []) (initial [false]) 2 =
    some (.inr (5,([],true,[false]))) := rfl
example : valid (program (false,false,0,1) []) = true := by decide
example : run (program (false,false,0,1) [])
    (initial (BitstringEncoding.bitEncode (([] : List Bool),[false,true]))) 14 =
      some (.inr (5,([],true,[true,false,false,true,true,false,false]))) := by decide
end Fixtures

end Shared.ComplexityBridge.PairReverseWitness
