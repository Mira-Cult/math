import Shared.Codes.RequestParseCosts

/-! Charged parsing of finite-program table syntax. Numeric fields remain
as binary payload lists; their natural-number interpretation is used only in
correctness statements. Validation and arithmetic are separate obligations. -/
namespace Shared.Codes.ProgramParseCosts

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBits
open Shared.Codes.BitBlockCosts
open Shared.Codes.RequestParseCosts
open Shared.ComplexityBridge.CNFWitness

def atomBool (bits : List Bool) : Option Bool × Nat :=
  (match bits with | [b] => some b | _ => none,1)

theorem atomBool_correct (bits : List Bool) : (atomBool bits).1 = (BitstringEncoding.bitDecode bits : Option Bool) := by
  cases bits with
  | nil => rfl
  | cons b rest => cases rest <;> rfl

theorem atomBool_steps (bits : List Bool) : (atomBool bits).2 ≤ 0*bits.length+1 := by simp [atomBool]

/-- Retain the actual numeric payload. No conversion to a machine integer is
performed by the parser. -/
def atomNatBits (bits : List Bool) : Option (List Bool) × Nat := (some bits,1)

theorem atomNatBits_correct (bits : List Bool) :
    (atomNatBits bits).1.map Computability.decodeNat = (BitstringEncoding.bitDecode bits : Option Nat) := rfl

theorem atomNatBits_steps (bits : List Bool) : (atomNatBits bits).2 ≤ 0*bits.length+1 := by simp [atomNatBits]

def mapPair {α β γ δ : Type} (f : α → γ) (g : β → δ) (p : α × β) : γ × δ := (f p.1,g p.2)

theorem pair_interpreted {α β γ δ : Type} [BitstringEncoding γ] [BitstringEncoding δ]
    (pa : List Bool → Option α × Nat) (pb : List Bool → Option β × Nat) (f : α → γ) (g : β → δ)
    (ha : ∀ bits, (pa bits).1.map f = BitstringEncoding.bitDecode bits)
    (hb : ∀ bits, (pb bits).1.map g = BitstringEncoding.bitDecode bits) (bits : List Bool) :
    (pair pa pb bits).1.map (mapPair f g) = (BitstringEncoding.bitDecode bits : Option (γ × δ)) := by
  change (pair pa pb bits).1.map (mapPair f g) = (match BitstringEncoding.undelimit bits with
    | none => none
    | some (left,right) => match (BitstringEncoding.bitDecode left : Option γ),
        (BitstringEncoding.bitDecode right : Option δ) with
      | some x,some y => some (x,y) | _,_ => none)
  have hf := readBlock_correct bits
  cases hr : (readBlock bits).1 with
  | none => simp [pair,hr,←hf]
  | some v =>
    rcases v with ⟨left,right⟩
    have hal := ha left
    have hbr := hb right
    cases hpa : (pa left).1 <;> cases hpb : (pb right).1 <;>
      simp [pair,hr,←hf,hpa,hpb,←hal,←hbr,mapPair]

abbrev BitRow := Bool × Bool × List Bool × List Bool
abbrev BitPair := BitRow × BitRow
abbrev BitProgram := List BitPair

def interpretRow (r : BitRow) : Row :=
  (r.1,r.2.1,Computability.decodeNat r.2.2.1,Computability.decodeNat r.2.2.2)

def interpretPair (p : BitPair) : Row × Row := (interpretRow p.1,interpretRow p.2)
def interpretProgram (p : BitProgram) : Program := p.map interpretPair

def rowParser (bits : List Bool) : Option BitRow × Nat :=
  pair atomBool (pair atomBool (pair atomNatBits atomNatBits)) bits

def rowPairParser (bits : List Bool) : Option BitPair × Nat := pair rowParser rowParser bits

theorem rowParser_correct (bits : List Bool) :
    (rowParser bits).1.map interpretRow = (BitstringEncoding.bitDecode bits : Option Row) := by
  have hb (b : List Bool) : (atomBool b).1.map id = (BitstringEncoding.bitDecode b : Option Bool) := by
    simpa using atomBool_correct b
  have h := pair_interpreted atomBool (pair atomBool (pair atomNatBits atomNatBits)) id
    (mapPair id (mapPair Computability.decodeNat Computability.decodeNat)) hb
    (pair_interpreted atomBool (pair atomNatBits atomNatBits) id
      (mapPair Computability.decodeNat Computability.decodeNat) hb
      (pair_interpreted atomNatBits atomNatBits Computability.decodeNat Computability.decodeNat
        atomNatBits_correct atomNatBits_correct)) bits
  have he : mapPair id (mapPair id (mapPair Computability.decodeNat Computability.decodeNat)) = interpretRow := by
    funext r
    rcases r with ⟨w,d,n,t⟩
    rfl
  simpa [rowParser,he] using h

theorem rowPairParser_correct (bits : List Bool) :
    (rowPairParser bits).1.map interpretPair = (BitstringEncoding.bitDecode bits : Option (Row × Row)) := by
  have he : mapPair interpretRow interpretRow = interpretPair := by funext p; cases p; rfl
  simpa [rowPairParser,he] using
    pair_interpreted rowParser rowParser interpretRow interpretRow rowParser_correct rowParser_correct bits

theorem rowParser_steps (bits : List Bool) : (rowParser bits).2 ≤ 3*bits.length+10 := by
  have hnat : ∀ b, (pair atomNatBits atomNatBits b).2 ≤ 1*b.length+4 := by
    intro b; simpa using pair_steps atomNatBits atomNatBits 0 1 0 1 atomNatBits_steps atomNatBits_steps b
  have htail : ∀ b, (pair atomBool (pair atomNatBits atomNatBits) b).2 ≤ 2*b.length+7 := by
    intro b; simpa using pair_steps atomBool (pair atomNatBits atomNatBits) 0 1 1 4 atomBool_steps hnat b
  simpa [rowParser] using pair_steps atomBool (pair atomBool (pair atomNatBits atomNatBits))
    0 1 2 7 atomBool_steps htail bits

theorem rowPairParser_steps (bits : List Bool) : (rowPairParser bits).2 ≤ 7*bits.length+22 := by
  simpa [rowPairParser] using pair_steps rowParser rowParser 3 10 3 10 rowParser_steps rowParser_steps bits

def traverse {α : Type} (parser : List Bool → Option α × Nat) : List (List Bool) → Option (List α) × Nat
  | [] => (some [],1)
  | block::rest =>
      let item := parser block
      match item.1 with
      | none => (none,1+item.2)
      | some a =>
          let tail := traverse parser rest
          (tail.1.map (a::·),1+item.2+tail.2)

theorem traverse_interpreted {α β : Type} [BitstringEncoding β]
    (parser : List Bool → Option α × Nat) (f : α → β)
    (h : ∀ bits, (parser bits).1.map f = BitstringEncoding.bitDecode bits) (blocks : List (List Bool)) :
    (traverse parser blocks).1.map (List.map f) = blocks.mapM (@BitstringEncoding.bitDecode β _) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    have hb := h block
    cases hp : (parser block).1 with
    | none => simp [traverse,hp,List.mapM_cons,←hb]
    | some a =>
      cases ht : (traverse parser rest).1 with
      | none => simp [traverse,hp,ht,List.mapM_cons,←hb,←ih]
      | some xs => simp [traverse,hp,ht,List.mapM_cons,←hb,←ih]

theorem traverse_steps {α : Type} (parser : List Bool → Option α × Nat) (c k : Nat)
    (h : ∀ bits, (parser bits).2 ≤ c*bits.length+k) (blocks : List (List Bool)) :
    (traverse parser blocks).2 ≤ (c+k+1)*(blocks.length+(blocks.map List.length).sum)+1 := by
  induction blocks with
  | nil => simp [traverse]
  | cons block rest ih =>
    have hb := h block
    simp only [Nat.mul_add] at ih
    have hc : c*block.length ≤ (c+k+1)*block.length := by
      exact Nat.mul_le_mul_right block.length (by omega)
    cases hp : (parser block).1 with
    | none =>
      simp only [traverse,hp,Prod.snd,List.length_cons,List.map_cons,List.sum_cons,Nat.mul_add]
      omega
    | some a =>
      simp only [traverse,hp,Prod.snd,List.length_cons,List.map_cons,List.sum_cons,Nat.mul_add]
      omega

def programParser (bits : List Bool) : Option BitProgram × Nat :=
  let framed := parseBlocks bits
  match framed.1 with
  | none => (none,1+framed.2)
  | some blocks =>
      let result := traverse rowPairParser blocks
      (result.1,1+framed.2+result.2)

theorem programParser_correct (bits : List Bool) :
    (programParser bits).1.map interpretProgram = parse bits := by
  change (programParser bits).1.map interpretProgram =
    (BitstringEncoding.undelimitBlocks bits).bind (·.mapM BitstringEncoding.bitDecode)
  have h := parseBlocks_correct bits
  cases hp : (parseBlocks bits).1 with
  | none => simp [programParser,hp,←h]
  | some blocks =>
    have he : List.map interpretPair = interpretProgram := by funext p; rfl
    simpa [programParser,hp,←h,he] using
      traverse_interpreted rowPairParser interpretPair rowPairParser_correct blocks

theorem programParser_steps (bits : List Bool) : (programParser bits).2 ≤ 32*bits.length+3 := by
  have hp := parseBlocks_steps bits
  cases hb : (parseBlocks bits).1 with
  | none => simp only [programParser,hb]; omega
  | some blocks =>
    have hs : BitstringEncoding.undelimitBlocks bits = some blocks := by rw [←parseBlocks_correct,hb]
    have hl := blocks_length_bound blocks
    rw [blocks_sound bits blocks hs] at hl
    have ht := traverse_steps rowPairParser 7 22 rowPairParser_steps blocks
    simp only [programParser,hb]
    omega

namespace Fixtures
example : (programParser []).1 = some [] := rfl
example : (programParser [true]).1 = none := by decide
example : (atomNatBits [false]).1.map Computability.decodeNat = some 2 := by decide
example : (programParser (serialize [((false,true,0,2),(true,false,4,1))])).1.map interpretProgram =
    some [((false,true,0,2),(true,false,4,1))] := by
  rw [programParser_correct,parse_serialize]
end Fixtures

end Shared.Codes.ProgramParseCosts
