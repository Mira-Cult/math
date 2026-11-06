import Shared.Beeping.NPcoNP.Source284CompileRecords
import Mathlib.Data.List.OfFn

/-! Structural traversal for the existing finite-program source compiler.
This is an identity for every finite program, including invalid ones. It
does not claim that invalid continuations preserve rejection, or that this
traversal has a polynomial-time implementation. -/
namespace Shared.Beeping.NPcoNP.Source284CompileRecordsList

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284CompileRecords

/-- In the source's indexed order: forward-zero, forward-one,
reverse-zero, reverse-one. -/
def rowBlock (size : Nat) (rows : Row × Row) : List Nat :=
  [encodedRow size false rows.1, encodedRow size false rows.2,
   encodedRow size true rows.1, encodedRow size true rows.2]

/-- The four rows of the reserved nonaccepting sink. -/
def sinkBlock (size : Nat) : List Nat :=
  [pack false false (rejectState size), pack true false (rejectState size),
   pack false true (rejectState size), pack true true (rejectState size)]

def recordsList (p : Program) : List Nat :=
  (p.map (rowBlock p.length)).flatten ++ sinkBlock p.length

private theorem block_state (p : Program) (q : Fin p.length) :
    List.ofFn (fun j : Fin 4 => recordAt p (4*q.val+j.val)) =
      rowBlock p.length p[q.val] := by
  apply List.ext_getElem
  · simp [rowBlock]
  · intro i hi hj
    have h4 : i < 4 := by simpa [rowBlock] using hj
    interval_cases i
    · simpa [rowBlock, recordIndex, bit] using recordAt_state p q.val false false q.isLt
    · simpa [rowBlock, recordIndex, bit] using recordAt_state p q.val false true q.isLt
    · simpa [rowBlock, recordIndex, bit] using recordAt_state p q.val true false q.isLt
    · simpa [rowBlock, recordIndex, bit] using recordAt_state p q.val true true q.isLt

private theorem block_sink (p : Program) :
    List.ofFn (fun j : Fin 4 => recordAt p (4*p.length+j.val)) = sinkBlock p.length := by
  apply List.ext_getElem
  · simp [sinkBlock]
  · intro i hi hj
    have h4 : i < 4 := by simpa [sinkBlock] using hj
    interval_cases i
    · simpa [sinkBlock, recordIndex, bit] using recordAt_sink p false false
    · simpa [sinkBlock, recordIndex, bit] using recordAt_sink p false true
    · simpa [sinkBlock, recordIndex, bit] using recordAt_sink p true false
    · simpa [sinkBlock, recordIndex, bit] using recordAt_sink p true true

/-- The indexed compiler is exactly a traversal over the concrete program
followed by its four sink records. No reification of Lean functions is used. -/
theorem records_eq_recordsList (p : Program) : records p = recordsList p := by
  unfold records
  rw [List.ofFn_mul']
  have hchunks : (List.ofFn fun q : Fin (p.length+1) =>
      List.ofFn fun j : Fin 4 => recordAt p (4*q.val+j.val)) =
      (p.map (rowBlock p.length)).concat (sinkBlock p.length) := by
    rw [List.ofFn_succ']
    congr 1
    · rw [← List.ofFn_getElem_eq_map p (rowBlock p.length)]
      congr 1
      funext q
      exact block_state p q
    · exact block_sink p
  rw [hchunks]
  simp [recordsList, List.concat_eq_append]

end Shared.Beeping.NPcoNP.Source284CompileRecordsList
