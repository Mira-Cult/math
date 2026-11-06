import Shared.Beeping.Machines
import FormalConjecturesForMathlib.Computability.BitstringEncoding

/-! Canonical, executable bit serialization of total binary transition tables.
The serialized tuple contains the start state, blank symbol, signed initial
head position, and exactly two rows with independent event flags for each
finite state. -/
namespace Shared.Beeping.TableBits
open Shared.Beeping.Machines

deriving instance DecidableEq for Shared.Beeping.Machines.Table
deriving instance DecidableEq for Shared.Beeping.Machines.Machine

abbrev RawRow := Bool × (Bool × (Nat × Bool))
abbrev RawPair := RawRow × RawRow
abbrev RawMachine := (Nat × (Bool × Int)) × List RawPair

def moveBit : Move → Bool | .left => false | .right => true
def bitMove : Bool → Move | false => .left | true => .right

@[simp] theorem bitMove_moveBit (m : Move) : bitMove (moveBit m) = m := by cases m <;> rfl

def rowData {n : Nat} (r : Row n) : RawRow := (r.write,(moveBit r.move,(r.next.val,r.beep)))

def data {n : Nat} (M : Machine n) : RawMachine :=
  ((M.start.val,(M.blank,M.startHead)),M.table.rows.toList.map (fun p => (rowData p.1,rowData p.2)))

def serialize {n : Nat} (M : Machine n) : List Bool := BitstringEncoding.bitEncode (data M)

def rowFromData {n : Nat} (fallback : Fin n) (r : RawRow) : Row n :=
  ⟨r.1,bitMove r.2.1,if h : r.2.2.1 < n then ⟨r.2.2.1,h⟩ else fallback,r.2.2.2⟩

@[simp] theorem rowFromData_rowData {n : Nat} (fallback : Fin n) (r : Row n) :
    rowFromData fallback (rowData r) = r := by
  cases r with
  | mk w m q b =>
    simp [rowFromData,rowData,bitMove_moveBit,q.isLt]

def defaultRaw : RawPair := ((false,(false,(0,false))),(false,(false,(0,false))))

def assemble {n : Nat} (d : RawMachine) (start : Fin n) : Machine n :=
  { start := start
    blank := d.1.2.1
    startHead := d.1.2.2
    table := ⟨Vector.ofFn fun i =>
      let p := (d.2[i.val]?).getD defaultRaw
      (rowFromData start p.1,rowFromData start p.2)⟩ }

/-- The reserialization check rejects wrong row counts and out-of-range
destination states, as well as a start state outside `Fin n`. -/
def parseData (n : Nat) (d : RawMachine) : Option (Machine n) :=
  if h : d.1.1 < n then
    let M := assemble d ⟨d.1.1,h⟩
    if data M = d then some M else none
  else none

def parse (n : Nat) (bits : List Bool) : Option (Machine n) := do
  let d ← (BitstringEncoding.bitDecode bits : Option RawMachine)
  parseData n d

theorem assemble_data {n : Nat} (M : Machine n) : assemble (data M) M.start = M := by
  cases M with
  | mk table start blank head =>
    cases table with
    | mk rows =>
      simp only [assemble,data]
      congr 2
      apply Vector.ext
      intro i hi
      simp [assemble,data,Vector.getElem_ofFn,List.getElem?_map,List.getElem?_eq_getElem,
        Vector.length_toList,Vector.getElem_toList,hi,rowFromData_rowData]

@[simp] theorem parseData_data {n : Nat} (M : Machine n) : parseData n (data M) = some M := by
  unfold parseData
  have h : (data M).1.1 < n := M.start.isLt
  simp only [h, dite_true]
  have he : (⟨(data M).1.1,h⟩ : Fin n) = M.start := Fin.ext rfl
  rw [he,assemble_data]
  simp

@[simp] theorem parse_serialize {n : Nat} (M : Machine n) : parse n (serialize M) = some M := by
  simp [parse,serialize,parseData_data]

/-- Successful parsing reserializes to the decoded tuple exactly. Thus a
hash of `bits` may identify the source, while this equality supplies its
semantic connection to the machine. -/
theorem parseData_sound {n : Nat} {d : RawMachine} {M : Machine n} (h : parseData n d = some M) :
    data M = d := by
  unfold parseData at h
  split at h
  · dsimp only at h
    split at h
    · cases h; assumption
    · simp at h
  · simp at h

theorem parse_sound {n : Nat} {bits : List Bool} {M : Machine n} (h : parse n bits = some M) :
    ∃ d : RawMachine, BitstringEncoding.bitDecode bits = some d ∧ data M = d := by
  unfold parse at h
  cases hd : (BitstringEncoding.bitDecode bits : Option RawMachine) with
  | none => simp [hd] at h
  | some d =>
    refine ⟨d,rfl,?_⟩
    exact parseData_sound (by simpa [hd] using h)

/-- Every emitted row destination lies in the finite state set. -/
def validRow (n : Nat) (r : RawRow) : Bool := decide (r.2.2.1 < n)
def validRows (n : Nat) (rows : List RawPair) : Bool :=
  rows.all fun p => validRow n p.1 && validRow n p.2

theorem data_rows_length {n : Nat} (M : Machine n) : (data M).2.length = n := by
  simp [data,Vector.length_toList]

theorem data_rows_valid {n : Nat} (M : Machine n) : validRows n (data M).2 = true := by
  simp only [data,validRows,List.all_eq_true,List.mem_map]
  intro pair hpair
  obtain ⟨rows,_,rfl⟩ := hpair
  simp [validRow,rowData,rows.1.next.isLt,rows.2.next.isLt]

/-- A successful parse cannot conceal a missing row or an invalid destination. -/
theorem parseData_valid {n : Nat} {d : RawMachine} {M : Machine n} (h : parseData n d = some M) :
    d.1.1 < n ∧ d.2.length = n ∧ validRows n d.2 = true := by
  have he := parseData_sound h
  rw [←he]
  exact ⟨M.start.isLt,data_rows_length M,data_rows_valid M⟩

/-- A deliberately simple byte representation: each Boolean is one byte,
`0x00` or `0x01`, in the same order as the canonical bitstring. This is
unambiguous and costs eight stored bits per serialized Boolean. -/
def byteOfBit (b : Bool) : UInt8 := if b then 1 else 0

def bitOfByte (b : UInt8) : Option Bool :=
  if b = 0 then some false else if b = 1 then some true else none

def serializeBytes {n : Nat} (M : Machine n) : List UInt8 := (serialize M).map byteOfBit

def parseBytes (n : Nat) (bytes : List UInt8) : Option (Machine n) := do
  let bits ← bytes.mapM bitOfByte
  parse n bits

theorem byte_roundtrip (bits : List Bool) : (bits.map byteOfBit).mapM bitOfByte = some bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [byteOfBit,bitOfByte,ih]

@[simp] theorem parseBytes_serializeBytes {n : Nat} (M : Machine n) :
    parseBytes n (serializeBytes M) = some M := by
  unfold parseBytes serializeBytes
  rw [byte_roundtrip]
  exact parse_serialize M

theorem serializeBytes_length {n : Nat} (M : Machine n) :
    (serializeBytes M).length = (serialize M).length := by simp [serializeBytes]

theorem parseBytes_sound {n : Nat} {bytes : List UInt8} {M : Machine n} (h : parseBytes n bytes = some M) :
    ∃ bits, bytes.mapM bitOfByte = some bits ∧ parse n bits = some M := by
  unfold parseBytes at h
  cases hd : bytes.mapM bitOfByte with
  | none => simp [hd] at h
  | some bits => exact ⟨bits,rfl,by simpa [hd] using h⟩

/-- Number of flagged transition rows, counting the two input symbols
separately. This is a model-budget parameter distinct from the state count. -/
def flagCount {n : Nat} (M : Machine n) : Nat :=
  (M.table.rows.toList.map (fun p => p.1.beep)).count true +
    (M.table.rows.toList.map (fun p => p.2.beep)).count true

theorem flagCount_le {n : Nat} (M : Machine n) : flagCount M ≤ 2*n := by
  have h₁ := List.count_le_length (a := true) (l := M.table.rows.toList.map (fun p => p.1.beep))
  have h₂ := List.count_le_length (a := true) (l := M.table.rows.toList.map (fun p => p.2.beep))
  simp only [List.length_map,Vector.length_toList] at h₁ h₂
  simp only [flagCount]
  omega

/-- Storage cost for the specified one-byte-per-bit representation. -/
def descriptionBits {n : Nat} (M : Machine n) : Nat := 8*(serializeBytes M).length

theorem descriptionBits_eq {n : Nat} (M : Machine n) : descriptionBits M = 8*(serialize M).length := by
  simp [descriptionBits,serializeBytes_length]

namespace Fixtures
example : parse 0 [] = none := by decide
example : bitOfByte 2 = none := by decide
example : parseBytes 1 [2] = none := by decide

def fixture : Machine 1 :=
  { table := ⟨#v[((⟨true,.left,⟨0,by decide⟩,true⟩ : Row 1),
      (⟨false,.right,⟨0,by decide⟩,true⟩ : Row 1))]⟩
    start := ⟨0,by decide⟩
    blank := true
    startHead := -2 }

example : parseBytes 1 (serializeBytes fixture) = some fixture := parseBytes_serializeBytes fixture
example : (parseBytes 1 (serializeBytes fixture)).isSome = true := by decide
example : parseData 1 ((0,(false,0)),[]) = none := by decide
example : parseData 1 ((1,(false,0)),[defaultRaw]) = none := by decide
example : parseData 1 ((0,(false,0)),[((false,(false,(1,false))),(false,(false,(0,false))))]) = none := by decide
example : (fixture.table.row ⟨0,by decide⟩ false).beep = true := rfl
example : (fixture.table.row ⟨0,by decide⟩ true).beep = true := rfl
example : flagCount fixture = 2 := rfl
end Fixtures
end Shared.Beeping.TableBits
