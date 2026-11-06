import Shared.Beeping.NPcoNP.Source284ListTables

/-! A single finite, canonically encoded representation for relative source
rows. Each row is `(write, turn, continues, destination)`; the destination is
ignored if `continues` is false. The tuple and list encodings are the existing
root `BitstringEncoding` product/list encodings. This adapter makes no
runtime or complexity claim. -/
namespace Shared.Beeping.NPcoNP.Source284EncodedRows

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284ListTables

abbrev EncRow := Bool × Bool × Bool × Nat
abbrev EncRows := List (EncRow × EncRow)

def decodeRow (r : EncRow) : Row :=
  ⟨r.1, r.2.1, if r.2.2.1 then some r.2.2.2 else none⟩

def encodeRow (r : Row) : EncRow :=
  (r.write, r.turn, r.next.isSome, r.next.getD 0)

/-- Terminal rows have no meaningful destination; normalization chooses zero. -/
def normalizeRow (r : EncRow) : EncRow :=
  (r.1, r.2.1, r.2.2.1, if r.2.2.1 then r.2.2.2 else 0)

def decodeRows (rows : EncRows) : Rows :=
  rows.map fun p => (decodeRow p.1, decodeRow p.2)

def encodeRows (rows : Rows) : EncRows :=
  rows.map fun p => (encodeRow p.1, encodeRow p.2)

@[simp] theorem decode_encode_row (r : Row) : decodeRow (encodeRow r) = r := by
  cases r with
  | mk w t n => cases n <;> rfl

@[simp] theorem encode_decode_row (r : EncRow) : encodeRow (decodeRow r) = normalizeRow r := by
  rcases r with ⟨w,t,c,n⟩
  cases c <;> rfl

@[simp] theorem decode_encode_rows (rows : Rows) : decodeRows (encodeRows rows) = rows := by
  induction rows with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    change (decodeRow (encodeRow a), decodeRow (encodeRow b)) ::
      decodeRows (encodeRows ps) = (a,b) :: ps
    simp only [decode_encode_row, ih]

@[simp] theorem decodeRows_length (rows : EncRows) : (decodeRows rows).length = rows.length := by
  simp [decodeRows]

@[simp] theorem encodeRows_length (rows : Rows) : (encodeRows rows).length = rows.length := by
  simp [encodeRows]

/-- In-range table lookup observes exactly the decoded tuple selected by the
read bit; no agreement is claimed with an arbitrary table outside the list. -/
theorem lookup (rows : EncRows) (q : Nat) (h : q < rows.length) (read : Bool) :
    Source284ListTables.table (decodeRows rows) q read =
      decodeRow (if read then rows[q].2 else rows[q].1) := by
  have h' : q < (decodeRows rows).length := by simpa using h
  rw [Source284ListTables.table_in_range _ _ h']
  cases read <;> simp [decodeRows]

end Shared.Beeping.NPcoNP.Source284EncodedRows
