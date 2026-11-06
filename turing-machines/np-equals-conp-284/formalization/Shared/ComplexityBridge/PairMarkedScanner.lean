import Shared.ComplexityBridge.PairInputScanner

/-! A concrete finite-program scan that marks the pair separator on the
binary tape. The marker enables a later reverse pass; construction of the
full translated input tape remains separate. -/
namespace Shared.ComplexityBridge.PairMarkedScanner
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

/-- States 0-4 implement the parser. The row taken at the final blank and
all rows from state 5 onward are supplied by the continuation. -/
def program (onEnd : Row) (continuation : Program) : Program :=
  [ ((true,true,2,0),(true,true,1,0)),
    ((false,true,0,0),(true,true,0,0)),
    (onEnd,(true,true,3,0)),
    ((false,true,4,0),(true,true,4,0)),
    ((false,true,2,0),(true,true,2,0)) ] ++ continuation

def tapeAt (left right : List Bool) : Tape := (left,right.head?.getD false,right.tail)
def consumed (left bits : List Bool) : List Bool := bits.reverse ++ left

theorem consumed_cons (left : List Bool) (b : Bool) (bits : List Bool) :
    consumed left (b::bits) = consumed (b::left) bits := by
  simp [consumed,List.reverse_cons,List.append_assoc]

theorem consumed_append (left xs ys : List Bool) :
    consumed (consumed left xs) ys = consumed left (xs ++ ys) := by
  simp [consumed,List.reverse_append,List.append_assoc]

/-- Replace the terminal delimiter bit with a true landmark. -/
def markedDelimit : List Bool → List Bool
  | [] => [true]
  | b::xs => true::b::markedDelimit xs

theorem marked_length (xs : List Bool) : (markedDelimit xs).length = (BitstringEncoding.delimit xs).length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [markedDelimit,BitstringEncoding.delimit,ih]

theorem first_true (e : Row) (tail : Program) (L xs : List Bool) :
    run (program e tail) (0,tapeAt L (true::xs)) 1 = some (.inr (1,tapeAt (true::L) xs)) := by
  simp [run,advance,step,program,tapeAt,moveTape]

theorem first_data (e : Row) (tail : Program) (L xs : List Bool) (b : Bool) :
    run (program e tail) (1,tapeAt L (b::xs)) 1 = some (.inr (0,tapeAt (b::L) xs)) := by
  cases b <;> simp [run,advance,step,program,tapeAt,moveTape]

theorem mark_end (e : Row) (tail : Program) (L xs : List Bool) :
    run (program e tail) (0,tapeAt L (false::xs)) 1 = some (.inr (2,tapeAt (true::L) xs)) := by
  simp [run,advance,step,program,tapeAt,moveTape]

theorem witness_true (e : Row) (tail : Program) (L xs : List Bool) :
    run (program e tail) (2,tapeAt L (true::xs)) 1 = some (.inr (3,tapeAt (true::L) xs)) := by
  simp [run,advance,step,program,tapeAt,moveTape]

theorem witness_data (e : Row) (tail : Program) (L xs : List Bool) (b : Bool) :
    run (program e tail) (3,tapeAt L (b::xs)) 1 = some (.inr (4,tapeAt (b::L) xs)) := by
  cases b <;> simp [run,advance,step,program,tapeAt,moveTape]

theorem witness_end (e : Row) (tail : Program) (L xs : List Bool) :
    run (program e tail) (4,tapeAt L (false::xs)) 1 = some (.inr (2,tapeAt (false::L) xs)) := by
  simp [run,advance,step,program,tapeAt,moveTape]

/-- Scan the first component and write the delimiter landmark. -/
theorem scan_first (e : Row) (tail : Program) (xs suffix L : List Bool) :
    run (program e tail) (0,tapeAt L (BitstringEncoding.delimit xs ++ suffix)) (2*xs.length+1) =
      some (.inr (2,tapeAt (consumed L (markedDelimit xs)) suffix)) := by
  induction xs generalizing L with
  | nil => simpa [BitstringEncoding.delimit,markedDelimit,consumed] using mark_end e tail L suffix
  | cons b xs ih =>
    simp only [BitstringEncoding.delimit,List.cons_append,List.length_cons,markedDelimit]
    rw [show 2*(xs.length+1)+1 = 1+(1+(2*xs.length+1)) by omega]
    rw [run_continue _ _ _ 1 _ (first_true e tail L _)]
    rw [run_continue _ _ _ 1 _ (first_data e tail (true::L) _ b)]
    simpa only [consumed_cons] using ih (b::true::L)

/-- Scan the second component without changing it. -/
theorem scan_witness (e : Row) (tail : Program) (ws L : List Bool) :
    run (program e tail) (2,tapeAt L (BitstringEncoding.bitEncode ws)) (3*ws.length) =
      some (.inr (2,tapeAt (consumed L (BitstringEncoding.bitEncode ws)) [])) := by
  induction ws generalizing L with
  | nil => change some _ = some _; rfl
  | cons b ws ih =>
    change run (program e tail) (2,tapeAt L (true::b::false::BitstringEncoding.bitEncode ws))
      (3*(ws.length+1)) = some (.inr (2,tapeAt (consumed L (true::b::false::BitstringEncoding.bitEncode ws)) []))
    rw [show 3*(ws.length+1) = 1+(1+(1+3*ws.length)) by omega]
    rw [run_continue _ _ _ 1 _ (witness_true e tail L _)]
    rw [run_continue _ _ _ 1 _ (witness_data e tail (true::L) _ b)]
    rw [run_continue _ _ _ 1 _ (witness_end e tail (b::true::L) _)]
    simpa only [consumed_cons] using ih (false::b::true::L)

/-- The marked tape representation of a canonical input pair. -/
def markedPair (x w : List Bool) : List Bool :=
  markedDelimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode w

theorem markedPair_length (x w : List Bool) :
    (markedPair x w).length = (BitstringEncoding.bitEncode (x,w)).length := by
  change (markedDelimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode w).length =
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode w).length
  simp [marked_length]

/-- A literal finite-program table scans a canonical pair and changes exactly
the first-component delimiter into a true landmark. The continuation row is
not executed during this segment. -/
theorem scan_pair (e : Row) (tail : Program) (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    run (program e tail) (initial input) input.length =
      some (.inr (2,tapeAt (consumed [] (markedPair x w)) [])) := by
  let a := BitstringEncoding.bitEncode x
  let b := BitstringEncoding.bitEncode w
  have hi : BitstringEncoding.bitEncode (x,w) = BitstringEncoding.delimit a ++ b := rfl
  have hlen : (BitstringEncoding.bitEncode (x,w)).length = 2*a.length+1+3*w.length := by
    rw [hi,List.length_append,BitstringEncoding.length_delimit]
    simp [b,Shared.ComplexityBridge.bitstring_list_encoded_length]
  have hinit : initial (BitstringEncoding.bitEncode (x,w)) = (0,tapeAt [] (BitstringEncoding.delimit a ++ b)) := by
    rw [hi]
    rfl
  dsimp only
  rw [hlen,hinit,run_continue _ _ _ _ _ (scan_first e tail a b [])]
  rw [scan_witness,consumed_append]
  rfl

/-- Choosing a left-moving continuation takes one more transition and begins
the reverse pass at the final encoded input bit. -/
theorem scan_and_enter_reverse (next : Nat) (tail : Program) (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    let e : Row := (false,false,next,0)
    let t := tapeAt (consumed [] (markedPair x w)) []
    run (program e tail) (initial input) (input.length+1) = some (.inr (next,moveTape true false t)) := by
  change advance (program (false,false,next,0) tail)
    (run (program (false,false,next,0) tail) (initial (BitstringEncoding.bitEncode (x,w)))
      (BitstringEncoding.bitEncode (x,w)).length) = _
  rw [scan_pair]
  simp [advance,step,program,tapeAt]

namespace Fixtures
example : markedPair [] [] = [true] := rfl
example : markedPair [] [false] = [true,true,false,false] := rfl
example : (program (false,false,0,1) []).length = 5 := rfl
example : valid (program (false,false,0,1) []) = true := by decide
example : run (program (false,false,0,1) []) (initial [false]) 1 =
    some (.inr (2,([true],false,[]))) := rfl
end Fixtures

end Shared.ComplexityBridge.PairMarkedScanner
