import Shared.Beeping.TableBits
import Shared.ComplexityBridge.ParserComputability
import Shared.Codes.Inputs

/-! Effective numeric syntax for the literal transition-table representation.
The integer head is decoded as its two natural components; this avoids
pretending that a finite semantic machine is already a primitive-recursive
output type. -/
namespace Shared.Beeping.TableSyntax
open Shared.Beeping.TableBits
open Shared.ComplexityBridge.ParserComputability

abbrev Syntax := (Nat × (Bool × (Nat × Nat))) × List RawPair

def decode (bits : List Bool) : Option Syntax := BitstringEncoding.bitDecode bits

def toData (s : Syntax) : RawMachine :=
  ((s.1.1,(s.1.2.1,(s.1.2.2.1 : Int) - (s.1.2.2.2 : Int))),s.2)

theorem decode_primrec : Primrec decode := by
  have hrow : Primrec (@BitstringEncoding.bitDecode RawRow _) :=
    bitDecode_pair_primrec bitDecode_bool_primrec
      (bitDecode_pair_primrec bitDecode_bool_primrec
        (bitDecode_pair_primrec bitDecode_nat_primrec bitDecode_bool_primrec))
  exact bitDecode_pair_primrec
    (bitDecode_pair_primrec bitDecode_nat_primrec
      (bitDecode_pair_primrec bitDecode_bool_primrec
        (bitDecode_pair_primrec bitDecode_nat_primrec bitDecode_nat_primrec)))
    (bitDecode_list_primrec (bitDecode_pair_primrec hrow hrow))

theorem decode_computable : Computable decode := decode_primrec.to_comp

/-- Decode a pair after applying an output map to one component. -/
theorem decode_pair_map {A B C : Type} [BitstringEncoding A] [BitstringEncoding B]
    [BitstringEncoding C] (f : B → C)
    (hf : ∀ xs, (BitstringEncoding.bitDecode xs : Option C) =
      (BitstringEncoding.bitDecode xs : Option B).map f) (xs : List Bool) :
    (BitstringEncoding.bitDecode xs : Option (A × C)) =
      (BitstringEncoding.bitDecode xs : Option (A × B)).map (fun p => (p.1,f p.2)) := by
  change (match BitstringEncoding.undelimit xs with
    | none => none
    | some (a,b) => match (BitstringEncoding.bitDecode a : Option A),
        (BitstringEncoding.bitDecode b : Option C) with
      | some x, some y => some (x,y)
      | _, _ => none) = (match BitstringEncoding.undelimit xs with
    | none => none
    | some (a,b) => match (BitstringEncoding.bitDecode a : Option A),
        (BitstringEncoding.bitDecode b : Option B) with
      | some x, some y => some (x,y)
      | _, _ => none).map (fun p : A × B => (p.1, f p.2))
  cases hu : BitstringEncoding.undelimit xs with
  | none => rfl
  | some p =>
    rcases p with ⟨a,b⟩
    dsimp only
    rw [hf b]
    cases (BitstringEncoding.bitDecode a : Option A) <;>
      cases (BitstringEncoding.bitDecode b : Option B) <;> rfl

theorem int_decode (xs : List Bool) : (BitstringEncoding.bitDecode xs : Option Int) =
    (BitstringEncoding.bitDecode xs : Option (Nat × Nat)).map
      (fun p => (p.1 : Int) - (p.2 : Int)) := by
  change (BitstringEncoding.bitDecode xs : Option (Nat × Nat)).bind
    (fun p => some ((p.1 : Int) - (p.2 : Int))) = _
  cases (BitstringEncoding.bitDecode xs : Option (Nat × Nat)) <;> rfl

theorem pair_decode {A B : Type} [BitstringEncoding A] [BitstringEncoding B] (xs : List Bool) :
    (BitstringEncoding.bitDecode xs : Option (A × B)) =
      (match BitstringEncoding.undelimit xs with
       | none => none
       | some (a,b) => match (BitstringEncoding.bitDecode a : Option A),
           (BitstringEncoding.bitDecode b : Option B) with
         | some x, some y => some (x,y)
         | _, _ => none) := rfl

theorem decoded_data (xs : List Bool) :
    (BitstringEncoding.bitDecode xs : Option RawMachine) = (decode xs).map toData := by
  unfold decode
  have h₁ := decode_pair_map (A := Bool) (fun p : Nat × Nat => (p.1 : Int) - (p.2 : Int)) int_decode
  have h₂ := decode_pair_map (A := Nat) (fun p : Bool × (Nat × Nat) => (p.1, (p.2.1 : Int) - (p.2.2 : Int))) h₁
  rw [pair_decode (A := Nat × (Bool × Int)) (B := List RawPair),
    pair_decode (A := Nat × (Bool × (Nat × Nat))) (B := List RawPair)]
  cases hu : BitstringEncoding.undelimit xs with
  | none => rfl
  | some p =>
    rcases p with ⟨a,b⟩
    dsimp only
    rw [h₂ a]
    cases (BitstringEncoding.bitDecode a : Option (Nat × (Bool × (Nat × Nat)))) <;>
      cases (BitstringEncoding.bitDecode b : Option (List RawPair)) <;> rfl

theorem parse_factor (n : Nat) (bits : List Bool) :
    TableBits.parse n bits = (decode bits).bind (fun s => TableBits.parseData n (toData s)) := by
  unfold TableBits.parse
  rw [decoded_data]
  cases decode bits <;> rfl


/-- The validation test only inspects finite natural-number syntax. -/
def valid (n : Nat) (s : Syntax) : Bool :=
  decide (s.1.1 < n) && decide (s.2.length = n) && validRows n s.2

theorem validRows_primrec : Primrec₂ validRows := by
  let A := Nat × List RawPair
  have hd : Primrec (fun r : RawRow => r.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hpair : Primrec (fun p : A × (RawPair × Bool) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hrow₁ : Primrec (fun p : A × (RawPair × Bool) => decide (p.2.1.1.2.2.1 < p.1.1)) :=
    Primrec.nat_lt.decide.comp (hd.comp (Primrec.fst.comp hpair)) (Primrec.fst.comp Primrec.fst)
  have hrow₂ : Primrec (fun p : A × (RawPair × Bool) => decide (p.2.1.2.2.2.1 < p.1.1)) :=
    Primrec.nat_lt.decide.comp (hd.comp (Primrec.snd.comp hpair)) (Primrec.fst.comp Primrec.fst)
  have hstep : Primrec₂ (fun p : A => fun q : RawPair × Bool =>
      (decide (q.1.1.2.2.1 < p.1) && decide (q.1.2.2.2.1 < p.1)) && q.2) :=
    (Primrec.and.comp (Primrec.and.comp hrow₁ hrow₂) (Primrec.snd.comp Primrec.snd)).to₂
  have hf := Primrec.list_foldr (Primrec.snd : Primrec (fun p : A => p.2))
    (Primrec.const true) hstep
  apply hf.to₂.of_eq
  intro n rows
  induction rows with
  | nil => rfl
  | cons p ps ih =>
    change List.foldr (fun b s => (decide (b.1.2.2.1 < n) && decide (b.2.2.2.1 < n)) && s) true ps = validRows n ps at ih
    change ((decide (p.1.2.2.1 < n) && decide (p.2.2.2.1 < n)) &&
      List.foldr (fun b s => (decide (b.1.2.2.1 < n) && decide (b.2.2.2.1 < n)) && s) true ps) = validRows n (p::ps)
    rw [ih]
    rfl

theorem valid_primrec : Primrec₂ valid := by
  let A := Nat × Syntax
  have hstart : Primrec (fun p : A => decide (p.2.1.1 < p.1)) :=
    Primrec.nat_lt.decide.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst
  have hlen : Primrec (fun p : A => decide (p.2.2.length = p.1)) :=
    Primrec.eq.decide.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst
  have hrows : Primrec (fun p : A => validRows p.1 p.2.2) :=
    validRows_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact (Primrec.and.comp (Primrec.and.comp hstart hlen) hrows).to₂

def decodeValid (n : Nat) (bits : List Bool) : Option Syntax := do
  let s ← decode bits
  if valid n s then some s else none

theorem decodeValid_primrec : Primrec₂ decodeValid := by
  let A := Nat × List Bool
  have hd : Primrec (fun p : A => decode p.2) := decode_primrec.comp Primrec.snd
  have hv : Primrec (fun p : A × Syntax => valid p.1.1 p.2) :=
    valid_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have choice := Primrec.cond hv (Primrec.option_some.comp Primrec.snd)
    (Primrec.const (none : Option Syntax))
  apply (Primrec.option_bind hd choice.to₂).to₂.of_eq
  intro n bits
  cases h : decode bits with
  | none => simp [decodeValid,h]
  | some s => cases hv : valid n s <;> simp [decodeValid,h,hv]

theorem decodeValid_computable : Computable (fun p : Nat × List Bool => decodeValid p.1 p.2) :=
  decodeValid_primrec.to_comp


/-- Reconstructing an in-range row does not alter its numeric data. -/
theorem rowData_rowFromData {n : Nat} (q : Fin n) (r : RawRow)
    (h : r.2.2.1 < n) : rowData (rowFromData q r) = r := by
  rcases r with ⟨w,m,d,b⟩
  cases m <;> simp [rowData,rowFromData,bitMove,moveBit,h]

theorem data_assemble_of_valid {n : Nat} (d : RawMachine) (q : Fin n)
    (hq : q.val = d.1.1) (hlen : d.2.length = n) (hrows : validRows n d.2 = true) :
    data (assemble d q) = d := by
  have hmem (r : RawPair) (hr : r ∈ d.2) : r.1.2.2.1 < n ∧ r.2.2.2.1 < n := by
    have h := (List.all_eq_true.mp hrows) r hr
    simpa [validRows,validRow] using h
  rcases d with ⟨⟨start,blank,head⟩,rows⟩
  simp only [data, assemble]
  congr 2
  apply List.ext_getElem
  · simp [Vector.length_toList,hlen]
  · intro i h₁ h₂
    have hm := hmem rows[i] (List.getElem_mem h₂)
    simp [Vector.getElem_toList,Vector.getElem_ofFn,List.getElem?_eq_getElem h₂,
      rowData_rowFromData _ _ hm.1,rowData_rowFromData _ _ hm.2]


theorem parseData_some_iff {n : Nat} (d : RawMachine) :
    (TableBits.parseData n d).isSome = true ↔
      d.1.1 < n ∧ d.2.length = n ∧ validRows n d.2 = true := by
  constructor
  · intro h
    cases hp : TableBits.parseData n d with
    | none => simp [hp] at h
    | some M => exact TableBits.parseData_valid hp
  · rintro ⟨hs,hlen,hr⟩
    have he := data_assemble_of_valid d ⟨d.1.1,hs⟩ rfl hlen hr
    unfold TableBits.parseData
    simp only [hs, dite_true, he, ↓reduceIte, Option.isSome_some]

theorem valid_iff_parseData (n : Nat) (s : Syntax) :
    valid n s = true ↔ (TableBits.parseData n (toData s)).isSome = true := by
  rw [parseData_some_iff]
  simp [valid,toData,Bool.and_eq_true, and_assoc]

theorem decodeValid_success_iff (n : Nat) (bits : List Bool) :
    (decodeValid n bits).isSome = (TableBits.parse n bits).isSome := by
  rw [parse_factor]
  cases hd : decode bits with
  | none => simp [decodeValid,hd]
  | some s =>
    cases hv : valid n s with
    | false =>
      have h := (valid_iff_parseData n s).not.mp (by simp [hv])
      cases hp : TableBits.parseData n (toData s) <;> simp_all [decodeValid]
    | true =>
      have h := (valid_iff_parseData n s).mp hv
      cases hp : TableBits.parseData n (toData s) <;> simp_all [decodeValid]

theorem parse_isSome_primrec : Primrec₂ (fun n bits => (TableBits.parse n bits).isSome) := by
  have h := Primrec.option_isSome.comp (decodeValid_primrec.comp Primrec.fst Primrec.snd)
  apply h.to₂.of_eq
  intro n bits
  exact decodeValid_success_iff n bits

theorem parse_isSome_computable : Computable (fun p : Nat × List Bool => (TableBits.parse p.1 p.2).isSome) :=
  parse_isSome_primrec.to_comp

theorem decodeValid_factor (n : Nat) (bits : List Bool) :
    TableBits.parse n bits = (decodeValid n bits).bind (fun s => TableBits.parseData n (toData s)) := by
  rw [parse_factor]
  cases hd : decode bits with
  | none => simp [decodeValid,hd]
  | some s =>
    cases hv : valid n s with
    | false =>
      have h := (valid_iff_parseData n s).not.mp (by simp [hv])
      cases hp : TableBits.parseData n (toData s) <;> simp_all [decodeValid]
    | true => simp [decodeValid,hd,hv]

theorem decodeValid_complete {n : Nat} {bits : List Bool} {M : Shared.Beeping.Machines.Machine n}
    (h : TableBits.parse n bits = some M) :
    ∃ s, decodeValid n bits = some s ∧ TableBits.parseData n (toData s) = some M := by
  rw [decodeValid_factor] at h
  cases hd : decodeValid n bits with
  | none => simp [hd] at h
  | some s => exact ⟨s, rfl, by simpa [hd] using h⟩

theorem decodeValid_sound {n : Nat} {bits : List Bool} {s : Syntax}
    (h : decodeValid n bits = some s) :
    ∃ M, TableBits.parse n bits = some M ∧ TableBits.parseData n (toData s) = some M := by
  have hs : valid n s = true := by
    unfold decodeValid at h
    cases hd : decode bits with
    | none => simp [hd] at h
    | some t =>
      cases hv : valid n t with
      | false => simp [hd,hv] at h
      | true => simp [hd,hv] at h; subst t; exact hv
  have hp := (valid_iff_parseData n s).mp hs
  cases hd : TableBits.parseData n (toData s) with
  | none => simp [hd] at hp
  | some M =>
    refine ⟨M, ?_, rfl⟩
    rw [decodeValid_factor, h]
    simpa using hd


/-- Every finite machine has a valid numeric description in this effective
enumeration. Invalid bitstrings are returned as `none`. -/
def enumerate (p : Nat × Nat) : Option Syntax :=
  decodeValid p.1 (Shared.Codes.Inputs.inputAt p.2)

theorem inputAt_primrec : Primrec Shared.Codes.Inputs.inputAt :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem enumerate_primrec : Primrec enumerate :=
  decodeValid_primrec.comp Primrec.fst (inputAt_primrec.comp Primrec.snd)

theorem enumerate_computable : Computable enumerate := enumerate_primrec.to_comp

theorem enumerate_covers {n : Nat} (M : Shared.Beeping.Machines.Machine n) :
    ∃ i s, enumerate (n,i) = some s ∧ TableBits.parseData n (toData s) = some M := by
  obtain ⟨i,hi⟩ := Shared.Codes.Inputs.covers (TableBits.serialize M)
  obtain ⟨s,hs,hp⟩ := decodeValid_complete (TableBits.parse_serialize M)
  exact ⟨i,s,by simpa [enumerate,hi] using hs,hp⟩


/-- Numeric row lookup is also primitive recursive; the flag returned is the
fixed row entry for the selected state and scanned bit. -/
def lookup (p : (Syntax × Nat) × Bool) : Option RawRow :=
  (p.1.1.2[p.1.2]?).map (fun rows => if p.2 then rows.2 else rows.1)

theorem lookup_primrec : Primrec lookup := by
  let A := (Syntax × Nat) × Bool
  have hget : Primrec (fun p : A => p.1.1.2[p.1.2]?) :=
    Primrec.list_getElem?.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have hrow : Primrec₂ (fun p : A => fun rows : RawPair => if p.2 then rows.2 else rows.1) := by
    have h := Primrec.cond (Primrec.snd.comp Primrec.fst : Primrec (fun p : A × RawPair => p.1.2))
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
    apply h.to₂.of_eq
    intro p rows
    cases p.2 <;> rfl
  exact Primrec.option_map hget hrow

theorem lookup_computable : Computable lookup := lookup_primrec.to_comp

theorem lookup_correct {n : Nat} {s : Syntax} {M : Shared.Beeping.Machines.Machine n}
    (h : TableBits.parseData n (toData s) = some M) (q : Fin n) (b : Bool) :
    lookup ((s,q.val),b) = some (rowData (M.table.row q b)) := by
  have hd := TableBits.parseData_sound h
  have hr : s.2 = (data M).2 := by simpa [toData] using (congrArg Prod.snd hd).symm
  unfold lookup
  rw [hr]
  cases b <;> simp [data,Shared.Beeping.Machines.Table.row,Vector.getElem_toList,
    q.isLt]


/-- Bytes are represented recursion-theoretically by their natural values.
Only 0 and 1 are part of the specified byte representation. -/
def natByteBit (v : Nat) : Option Bool :=
  if v = 0 then some false else if v = 1 then some true else none

theorem natByteBit_primrec : Primrec natByteBit := by
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const (some false))
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const (some true))
      (Primrec.const none))

theorem natByteBit_eq (b : UInt8) : natByteBit b.toNat = TableBits.bitOfByte b := by
  have hzero : b.toNat = 0 ↔ b = 0 := by simpa using (UInt8.toNat_inj (a := b) (b := 0))
  have hone : b.toNat = 1 ↔ b = 1 := by simpa using (UInt8.toNat_inj (a := b) (b := 1))
  simp [natByteBit,TableBits.bitOfByte,hzero,hone]

def decodeNatBytes (n : Nat) (bytes : List Nat) : Option Syntax := do
  let bits ← bytes.mapM natByteBit
  decodeValid n bits

theorem decodeNatBytes_primrec : Primrec₂ decodeNatBytes := by
  have hb : Primrec (fun p : Nat × List Nat => p.2.mapM natByteBit) :=
    (list_mapM_primrec natByteBit_primrec).comp Primrec.snd
  have hd : Primrec₂ (fun p : Nat × List Nat => fun bits => decodeValid p.1 bits) :=
    (decodeValid_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.option_bind hb hd).to₂

theorem decodeNatBytes_computable : Computable (fun p : Nat × List Nat => decodeNatBytes p.1 p.2) :=
  decodeNatBytes_primrec.to_comp

theorem byteMap (bytes : List UInt8) :
    (bytes.map UInt8.toNat).mapM natByteBit = bytes.mapM TableBits.bitOfByte := by
  induction bytes with
  | nil => rfl
  | cons b bs ih => simp [List.mapM_cons,natByteBit_eq,ih]

theorem parseBytes_factor (n : Nat) (bytes : List UInt8) :
    TableBits.parseBytes n bytes =
      (decodeNatBytes n (bytes.map UInt8.toNat)).bind (fun s => TableBits.parseData n (toData s)) := by
  unfold TableBits.parseBytes decodeNatBytes
  rw [byteMap]
  cases h : bytes.mapM TableBits.bitOfByte with
  | none => rfl
  | some bits => simpa [h] using decodeValid_factor n bits

theorem parseBytes_success_iff (n : Nat) (bytes : List UInt8) :
    (decodeNatBytes n (bytes.map UInt8.toNat)).isSome = (TableBits.parseBytes n bytes).isSome := by
  unfold TableBits.parseBytes decodeNatBytes
  rw [byteMap]
  cases h : bytes.mapM TableBits.bitOfByte with
  | none => rfl
  | some bits => simpa [h] using decodeValid_success_iff n bits

namespace Fixtures
example : decodeValid 0 [] = none := by decide
example : decodeNatBytes 1 [2] = none := by decide
example : decodeNatBytes 1 [256] = none := by decide
example : (decodeValid 1 (TableBits.serialize TableBits.Fixtures.fixture)).isSome = true := by decide
example : (TableBits.parse 1 (TableBits.serialize TableBits.Fixtures.fixture)).isSome = true := by decide
example : valid 1 ((0,(false,(0,0))),[]) = false := by decide
example : valid 1 ((0,(false,(0,0))),[((false,(false,(1,false))),(false,(false,(0,false))))]) = false := by decide
end Fixtures

end Shared.Beeping.TableSyntax
