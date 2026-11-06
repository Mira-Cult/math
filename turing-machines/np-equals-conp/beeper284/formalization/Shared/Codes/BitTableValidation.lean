import Shared.Codes.BitNumeralCompare

/-! Bit-list table validation components. The cost counters measure recursive
list inspections and exclude their own arithmetic and machine simulation. -/
namespace Shared.Codes.BitTableValidation

open Shared.Codes.FinitePrograms
open Shared.Codes.ProgramParseCosts
open Shared.Codes.BitNumeralCompare
open Shared.Codes.FiniteProgramBits
open Shared.Codes.BitBlockCosts
open Shared.Codes.RequestParseCosts
open Shared.ComplexityBridge.CNFWitness

/-- Little-endian binary increment; [] represents zero. -/
def increment : List Bool → List Bool × Nat
  | [] => ([true],1)
  | false::bs => (true::bs,1)
  | true::bs => let r := increment bs; (false::r.1,1+r.2)

theorem increment_value (bits : List Bool) : value (increment bits).1 = value bits+1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [increment,value,ih] <;> omega

theorem increment_length (bits : List Bool) : (increment bits).1.length ≤ bits.length+1 := by
  induction bits with
  | nil => simp [increment]
  | cons b bs ih => cases b <;> simp [increment] at * <;> omega

theorem increment_steps (bits : List Bool) : (increment bits).2 ≤ bits.length+1 := by
  induction bits with
  | nil => simp [increment]
  | cons b bs ih => cases b <;> simp [increment] at * <;> omega

def countBits {α : Type} : List α → List Bool × Nat
  | [] => ([],1)
  | _::xs =>
      let r := countBits xs
      let next := increment r.1
      (next.1,1+r.2+next.2)

theorem countBits_value {α : Type} (xs : List α) : value (countBits xs).1 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [countBits,increment_value,List.length_cons,ih]

theorem countBits_length {α : Type} (xs : List α) : (countBits xs).1.length ≤ xs.length := by
  induction xs with
  | nil => simp [countBits]
  | cons x xs ih =>
    have h := increment_length (countBits xs).1
    simp only [countBits,List.length_cons]
    omega

theorem countBits_steps {α : Type} (xs : List α) : (countBits xs).2 ≤ (xs.length+1)*(xs.length+1) := by
  induction xs with
  | nil => simp [countBits]
  | cons x xs ih =>
    have hlen := countBits_length xs
    have hinc := increment_steps (countBits xs).1
    simp only [countBits,List.length_cons]
    simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.mul_add] at *
    omega

/-- Validate one row using binary comparison only. The counter is proof
instrumentation; both tag comparisons and the next-state comparison run. -/
def checkRow (bound : List Bool) (row : BitRow) : Bool × Nat :=
  let tag2 := compareRawCost row.2.2.2 [false,true]
  let tag0 := compareRawCost row.2.2.2 []
  let next := normalizeCost row.2.2.1
  let nextCmp := compareCost next.1 bound
  (decide (tag2.1 ≠ .gt) && (decide (tag0.1 ≠ .eq) || decide (nextCmp.1 = .lt)),
    1+tag2.2+tag0.2+next.2+nextCmp.2)

theorem checkRow_correct (bound : List Bool) (row : BitRow) :
    (checkRow bound row).1 = validRow (value bound) (interpretRow row) := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkRow,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
    compareRawCost_correct,compareCost_correct,compareBits_correct,normalizeCost_correct,value_normalize,
    compare_gt_iff_gt,compare_eq_iff_eq,compare_lt_iff_lt,validRow,interpretRow]
  have htwo : Computability.decodeNat [false,true] = 2 := by decide
  have hzero : Computability.decodeNat [] = 0 := rfl
  simp only [htwo,hzero,ne_eq,compare_gt_iff_gt,compare_eq_iff_eq,decide_eq_true_iff, bne_iff_ne]
  by_cases ht : Computability.decodeNat row.2.2.2 ≤ 2 <;>
    by_cases hn : Computability.decodeNat row.2.2.1 < value bound <;>
      simp [ht,hn] <;> omega

theorem checkRow_steps (bound : List Bool) (row : BitRow) :
    (checkRow bound row).2 ≤ 4*row.2.2.2.length+2*row.2.2.1.length+bound.length+30 := by
  have h2 := compareRawCost_steps row.2.2.2 [false,true]
  have h0 := compareRawCost_steps row.2.2.2 []
  have hn := normalizeCost_steps row.2.2.1
  have hl : (normalizeCost row.2.2.1).1.length ≤ row.2.2.1.length+1 := by
    rw [normalizeCost_correct]
    exact Shared.ComplexityBridge.NumeralNormalization.normalize_length _
  have hc := compareCost_steps (normalizeCost row.2.2.1).1 bound
  simp only [checkRow,List.length_cons,List.length_nil] at *
  omega

def rowWeight (row : BitRow) : Nat := row.2.2.1.length+row.2.2.2.length
def pairWeight (rows : BitPair) : Nat := rowWeight rows.1+rowWeight rows.2
def tableWeight (rows : BitProgram) : Nat := (rows.map pairWeight).sum

def checkRows (bound : List Bool) : BitProgram → Bool × Nat
  | [] => (true,1)
  | rows::rest =>
      let a := checkRow bound rows.1
      let b := checkRow bound rows.2
      let tail := checkRows bound rest
      (a.1 && b.1 && tail.1,1+a.2+b.2+tail.2)

theorem checkRows_correct (bound : List Bool) (rows : BitProgram) :
    (checkRows bound rows).1 = (interpretProgram rows).all
      (fun p => validRow (value bound) p.1 && validRow (value bound) p.2) := by
  induction rows with
  | nil => rfl
  | cons pair rest ih =>
    simp [checkRows,interpretProgram,interpretPair,checkRow_correct,ih]

theorem checkRows_steps (bound : List Bool) (rows : BitProgram) :
    (checkRows bound rows).2 ≤ 4*tableWeight rows+2*rows.length*bound.length+61*rows.length+1 := by
  induction rows with
  | nil => simp [checkRows,tableWeight]
  | cons pair rest ih =>
    have ha := checkRow_steps bound pair.1
    have hb := checkRow_steps bound pair.2
    simp only [checkRows,tableWeight,List.map_cons,List.sum_cons,List.length_cons,
      Nat.succ_eq_add_one,Nat.add_mul,Nat.mul_add,pairWeight,rowWeight] at *
    omega

def checkProgram (rows : BitProgram) : Bool × Nat :=
  let count := countBits rows
  let checked := checkRows count.1 rows
  (!rows.isEmpty && checked.1,1+count.2+checked.2)

theorem checkProgram_correct (rows : BitProgram) : (checkProgram rows).1 = valid (interpretProgram rows) := by
  have hcount := countBits_value rows
  have hrows := checkRows_correct (countBits rows).1 rows
  simp only [checkProgram,hrows,hcount,valid,interpretProgram,List.length_map,List.isEmpty_map]

/-- Quadratic charged list work in the number of rows, plus linear work in
the numeric payload sizes. Counter arithmetic itself is not charged here. -/
theorem checkProgram_steps (rows : BitProgram) :
    (checkProgram rows).2 ≤ (rows.length+1)*(rows.length+1)+4*tableWeight rows+
      2*rows.length*rows.length+61*rows.length+2 := by
  have hc := countBits_steps rows
  have hl := countBits_length rows
  have hr := checkRows_steps (countBits rows).1 rows
  have hm := Nat.mul_le_mul_left (2*rows.length) hl
  simp only [checkProgram]
  omega

/-- A successful pair parser cannot produce more payload bits than it read. -/
theorem pair_weight {α β : Type} (pa : List Bool → Option α × Nat) (pb : List Bool → Option β × Nat)
    (wa : α → Nat) (wb : β → Nat)
    (ha : ∀ bits a, (pa bits).1 = some a → wa a ≤ bits.length)
    (hb : ∀ bits b, (pb bits).1 = some b → wb b ≤ bits.length)
    (bits : List Bool) (a : α) (b : β) (h : (pair pa pb bits).1 = some (a,b)) :
    wa a+wb b ≤ bits.length := by
  cases hr : (readBlock bits).1 with
  | none => simp [pair,hr] at h
  | some v =>
    rcases v with ⟨left,right⟩
    cases hl : (pa left).1 with
    | none => simp [pair,hr,hl] at h
    | some x =>
      cases hn : (pb right).1 with
      | none => simp [pair,hr,hl,hn] at h
      | some y =>
        simp only [pair,hr,hl,hn,Prod.fst,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        have hx := ha left x hl
        have hy := hb right y hn
        have hd : BitstringEncoding.undelimit bits = some (left,right) := by rw [←readBlock_correct,hr]
        have he := congrArg List.length (undelimit_sound bits left right hd)
        simp only [List.length_append,BitstringEncoding.length_delimit] at he
        omega

theorem rowParser_weight (bits : List Bool) (row : BitRow) (h : (rowParser bits).1 = some row) :
    rowWeight row ≤ bits.length := by
  have hb : ∀ bits b, (atomBool bits).1 = some b → (fun _ : Bool => 0) b ≤ bits.length := by
    intro bits b h
    exact Nat.zero_le _
  have hn : ∀ bits b, (atomNatBits bits).1 = some b → b.length ≤ bits.length := by
    intro bits b h
    simp [atomNatBits] at h
    subst b
    exact le_rfl
  have hp : ∀ bits (p : List Bool × List Bool), (pair atomNatBits atomNatBits bits).1 = some p →
      p.1.length+p.2.length ≤ bits.length := by
    intro bits p h
    exact pair_weight atomNatBits atomNatBits List.length List.length hn hn bits p.1 p.2 (by simpa using h)
  have ht : ∀ bits (p : Bool × List Bool × List Bool),
      (pair atomBool (pair atomNatBits atomNatBits) bits).1 = some p →
      p.2.1.length+p.2.2.length ≤ bits.length := by
    intro bits p h
    have hh := pair_weight atomBool (pair atomNatBits atomNatBits) (fun _ => 0)
      (fun q => q.1.length+q.2.length) hb hp bits p.1 p.2 (by simpa using h)
    simpa using hh
  have hh := pair_weight atomBool (pair atomBool (pair atomNatBits atomNatBits)) (fun _ => 0)
    (fun q => q.2.1.length+q.2.2.length) hb ht bits row.1 row.2 (by simpa [rowParser] using h)
  simpa [rowWeight] using hh

theorem rowPairParser_weight (bits : List Bool) (rows : BitPair) (h : (rowPairParser bits).1 = some rows) :
    pairWeight rows ≤ bits.length := by
  exact pair_weight rowParser rowParser rowWeight rowWeight rowParser_weight rowParser_weight
    bits rows.1 rows.2 (by simpa [rowPairParser] using h)

theorem traverse_weight (blocks : List (List Bool)) (rows : BitProgram)
    (h : (Shared.Codes.ProgramParseCosts.traverse rowPairParser blocks).1 = some rows) :
    tableWeight rows ≤ (blocks.map List.length).sum := by
  induction blocks generalizing rows with
  | nil => simp [Shared.Codes.ProgramParseCosts.traverse] at h; subst rows; rfl
  | cons block rest ih =>
    cases hp : (rowPairParser block).1 with
    | none => simp [Shared.Codes.ProgramParseCosts.traverse,hp] at h
    | some first =>
      cases ht : (Shared.Codes.ProgramParseCosts.traverse rowPairParser rest).1 with
      | none => simp [Shared.Codes.ProgramParseCosts.traverse,hp,ht] at h
      | some tail =>
        simp [Shared.Codes.ProgramParseCosts.traverse,hp,ht] at h
        subst rows
        have hf := rowPairParser_weight block first hp
        have hs := ih tail ht
        simp only [tableWeight,List.map_cons,List.sum_cons] at *
        omega

theorem programParser_weight (bits : List Bool) (rows : BitProgram)
    (h : (programParser bits).1 = some rows) : tableWeight rows ≤ bits.length := by
  cases hp : (parseBlocks bits).1 with
  | none => simp [programParser,hp] at h
  | some blocks =>
    have ht : (Shared.Codes.ProgramParseCosts.traverse rowPairParser blocks).1 = some rows := by simpa [programParser,hp] using h
    have hw := traverse_weight blocks rows ht
    have hs : BitstringEncoding.undelimitBlocks bits = some blocks := by rw [←parseBlocks_correct,hp]
    have hl := blocks_length_bound blocks
    rw [blocks_sound bits blocks hs] at hl
    omega

theorem programParser_count (bits : List Bool) (rows : BitProgram)
    (h : (programParser bits).1 = some rows) : rows.length ≤ bits.length := by
  have hd := programParser_correct bits
  rw [h] at hd
  have hs : parse bits = some (interpretProgram rows) := by simpa using hd.symm
  have hn := parse_state_count bits (interpretProgram rows) hs
  simpa [interpretProgram] using hn

def parseAndCheck (bits : List Bool) : Option BitProgram × Nat :=
  let parsed := programParser bits
  match parsed.1 with
  | none => (none,1+parsed.2)
  | some rows =>
      let checked := checkProgram rows
      (if checked.1 then some rows else none,1+parsed.2+checked.2)

theorem parseAndCheck_correct (bits : List Bool) :
    (parseAndCheck bits).1.map interpretProgram = parseValid bits := by
  have hd := programParser_correct bits
  cases hp : (programParser bits).1 with
  | none =>
    have hs : parse bits = none := by rw [←hd,hp]; rfl
    simp [parseAndCheck,hp,parseValid,hs]
  | some rows =>
    have hs : parse bits = some (interpretProgram rows) := by rw [←hd,hp]; rfl
    have hv := checkProgram_correct rows
    cases hc : (checkProgram rows).1 <;>
      simp [parseAndCheck,hp,parseValid,hs,←hv,hc]

/-- Polynomial charged list-operation bound for parsing and validating the
binary table; numerical payloads remain bit lists throughout execution. -/
theorem parseAndCheck_steps (bits : List Bool) :
    (parseAndCheck bits).2 ≤ (bits.length+1)*(bits.length+1)+
      2*bits.length*bits.length+97*bits.length+6 := by
  have hp := programParser_steps bits
  cases hr : (programParser bits).1 with
  | none =>
    simp only [parseAndCheck,hr,Prod.snd]
    omega
  | some rows =>
    have hn := programParser_count bits rows hr
    have hw := programParser_weight bits rows hr
    have hc := checkProgram_steps rows
    have hsquare : (rows.length+1)*(rows.length+1) ≤ (bits.length+1)*(bits.length+1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hmul : rows.length*rows.length ≤ bits.length*bits.length := Nat.mul_le_mul hn hn
    have hmul2 : 2*rows.length*rows.length ≤ 2*bits.length*bits.length := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hmul
    simp only [parseAndCheck,hr,Prod.snd]
    omega

namespace Fixtures
example : (checkProgram []).1 = false := by decide
example : (checkRow [true] (false,true,[true],[])).1 = false := by
  rw [checkRow_correct]
  decide
example : (checkRow [true] (false,true,[],[false])).1 = true := by
  rw [checkRow_correct]
  decide
example : (parseAndCheck (serialize [((false,true,0,2),(true,false,0,1))])).1.map interpretProgram =
    some [((false,true,0,2),(true,false,0,1))] := by
  rw [parseAndCheck_correct,parseValid_serialize _ (by decide)]
example : (parseAndCheck (serialize ([] : Program))).1.map interpretProgram = none := by
  rw [parseAndCheck_correct]
  exact parseValid_invalid _ [] (parse_serialize []) (by decide)
end Fixtures

end Shared.Codes.BitTableValidation
