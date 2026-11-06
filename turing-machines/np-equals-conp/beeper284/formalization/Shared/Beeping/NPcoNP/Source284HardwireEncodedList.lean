import Shared.Beeping.NPcoNP.Source284HardwireListRows
import Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
import Mathlib.Data.List.OfFn

/-! A tuple-valued, structural input loader. Its prefix pays for the input
write/turn/rewind steps; its suffix maps the existing relocation worker over
the finite pre-guarded table. This file makes no complexity claim. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireEncodedList

open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2

/-- The loader-only rows, on a state known to be below its offset. -/
def loaderRow (bits : List Bool) (q : Nat) (read : Bool) : EncRow :=
  if q < bits.length then ((bits[q]?).getD false, false, true, q+1)
  else if q = bits.length then (false, true, true, q+1)
  else if q < 2*bits.length+1 then (read, false, true, q+1)
  else (read, true, true, q+1)

def loaderPair (bits : List Bool) (q : Nat) : EncRow × EncRow :=
  (loaderRow bits q false, loaderRow bits q true)

/-- The encoded prefix is constructed independently of the supplied rows;
the suffix relocates every stored pair with the shared tuple worker. -/
def rows (bits : List Bool) (original : EncRows) : EncRows :=
  (List.ofFn fun q : Fin (offset bits) => loaderPair bits q.val) ++
    original.map (fun pair => shiftPair (offset bits, pair))

@[simp] theorem rows_length (bits : List Bool) (original : EncRows) :
    (rows bits original).length = offset bits + original.length := by
  simp only [rows, List.length_append, List.length_ofFn, List.length_map]

private theorem loaderRow_correct (bits : List Bool) (original : EncRows)
    (q : Nat) (hq : q < offset bits) (read : Bool) :
    decodeRow (loaderRow bits q read) =
      Source284HardwireTable.table bits
        (Source284ListTables.table (decodeRows original)) q read := by
  unfold loaderRow Source284HardwireTable.table
  split_ifs <;> simp [decodeRow] at * <;> simp [offset] at * <;> omega

/-- Decoding the explicitly constructed tuple list yields exactly the
semantic loader materialization. The statement does not identify ignored
destination fields on terminal encoded rows. -/
theorem decode_rows (bits : List Bool) (original : EncRows) :
    decodeRows (rows bits original) =
      Source284HardwireListRows.rows bits (decodeRows original) := by
  have hs : Source284HardwireListRows.rows bits (decodeRows original) =
      List.ofFn (fun q : Fin (offset bits + original.length) =>
        (Source284HardwireTable.table bits (Source284ListTables.table (decodeRows original)) q.val false,
         Source284HardwireTable.table bits (Source284ListTables.table (decodeRows original)) q.val true)) := by
    simp only [Source284HardwireListRows.rows, decodeRows_length]
    congr 1
  rw [hs, List.ofFn_add]
  simp only [decodeRows, rows, List.map_append, List.map_map, List.map_ofFn, Function.comp_def]
  rw [← List.ofFn_getElem_eq_map original
    (fun p => (decodeRow (shiftPair (offset bits, p)).1,
      decodeRow (shiftPair (offset bits, p)).2))]
  congr 1
  · apply congrArg List.ofFn
    funext q
    simp only [Function.comp_apply, loaderPair, Fin.val_castLE]
    exact Prod.ext (loaderRow_correct bits original q q.isLt false)
      (loaderRow_correct bits original q q.isLt true)
  · apply congrArg List.ofFn
    funext q
    simp only [Function.comp_apply, Fin.val_natAdd, shiftPair, decode_shiftEncoded,
      relocated_row, Nat.add_sub_cancel_left]
    have hf := Source284EncodedRows.lookup original q q.isLt false
    have ht := Source284EncodedRows.lookup original q q.isLt true
    simp only [Bool.false_eq_true, ↓reduceIte, ite_true, decodeRows] at hf ht
    simp only [hf, ht]

end Shared.Beeping.NPcoNP.Source284HardwireEncodedList
