import Shared.Beeping.NPcoNP.Source284HardwireEncodedList
import Shared.Beeping.NPcoNP.Source284IndexedListFacts

/-! Loader prefix traversing the actual bit input twice. Each traversal is
paid for by that finite list; there is no free binary length expansion. The
present file defines the construction but makes no complexity claim. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireIndexedList

open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
open Shared.ComplexityBridge.TM2IndexedMap
open Shared.Beeping.NPcoNP.Source284IndexedListFacts
open Shared.Beeping.NPcoNP.Source284HardwireEncodedList (loaderPair loaderRow)

/-- Write the fixed bit, without changing direction. -/
def writePair (p : Nat × Bool) : EncRow × EncRow :=
  ((p.2, false, true, p.1+1), (p.2, false, true, p.1+1))

/-- Rewind without changing the scanned symbol. The traversed input bit is
used solely as one unit of finite fuel. -/
def rewindPair (p : Nat × Bool) : EncRow × EncRow :=
  ((false, false, true, p.1+1), (true, false, true, p.1+1))

def loaderPrefix (bits : List Bool) : EncRows :=
  indexed writePair 0 bits ++
  [((false,true,true,bits.length+1), (false,true,true,bits.length+1))] ++
  indexed rewindPair (bits.length+1) bits ++
  [((false,true,true,offset bits), (true,true,true,offset bits))]

def rows (bits : List Bool) (original : EncRows) : EncRows :=
  loaderPrefix bits ++ original.map (fun pair => shiftPair (offset bits, pair))

/-- The paid traversal lists the same loader states in the same order as
its bounded indexed specification. -/
theorem loaderPrefix_eq (bits : List Bool) :
    loaderPrefix bits = List.ofFn (fun q : Fin (offset bits) => loaderPair bits q.val) := by
  apply List.ext_getElem
  · simp [loaderPrefix, offset] <;> omega
  · intro q hleft hright
    have hq : q < offset bits := by simpa only [List.length_ofFn] using hright
    simp only [loaderPrefix] at hleft ⊢
    simp only [List.getElem_ofFn, Fin.val_mk]
    by_cases hw : q < bits.length
    · simp [loaderPrefix, List.getElem_append, getElem_indexed, loaderPair,
        loaderRow, writePair, hw]
    · by_cases ht : q = bits.length
      · subst q
        simp [loaderPrefix, List.getElem_append, getElem_indexed, loaderPair,
          loaderRow, writePair]
      · by_cases hr : q < 2*bits.length+1
        · have hq0 : bits.length + 1 ≤ q := by omega
          have hq1 : q - bits.length - 1 < bits.length := by omega
          simp [loaderPrefix, List.getElem_append, getElem_indexed, loaderPair,
            loaderRow, rewindPair, hw, ht, hr, hq0, hq1]
          have hj : q - (bits.length+1) < bits.length := by omega
          have hpos : q - bits.length = (q-(bits.length+1))+1 := by omega
          have hend : bits.length+1+(q-(bits.length+1))+1 = q+1 := by omega
          simp [hpos, List.getElem_append, getElem_indexed, hj, rewindPair, hend]
        · have hlast : q = 2*bits.length+1 := by simp [offset] at hq; omega
          have hq0 : bits.length + 1 ≤ q := by omega
          have hq1 : q - (bits.length + 1) = bits.length := by omega
          have hsub : q - bits.length = bits.length + 1 := by omega
          have hnext : q + 1 = offset bits := by simp [offset]; omega
          simp [-List.ofFn_succ, loaderPrefix, List.getElem_append, getElem_indexed,
            loaderPair, loaderRow, hw, ht, hr, hq0, hq1, hsub, hnext]

/-- The structural indexed implementation has the same decoded rows as the
semantic hardwire materialization. -/
theorem decode_rows (bits : List Bool) (original : EncRows) :
    decodeRows (rows bits original) =
      Source284HardwireListRows.rows bits (decodeRows original) := by
  unfold rows
  rw [loaderPrefix_eq]
  exact Source284HardwireEncodedList.decode_rows bits original

/-- Even with no input bits, both paid turn states remain. -/
example : loaderPrefix [] = [((false,true,true,1), (false,true,true,1)),
    ((false,true,true,2), (true,true,true,2))] := by rfl

end Shared.Beeping.NPcoNP.Source284HardwireIndexedList
