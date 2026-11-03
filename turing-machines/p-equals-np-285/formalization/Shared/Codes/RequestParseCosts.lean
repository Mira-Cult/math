import Shared.Codes.BitBlockCosts
import Shared.ComplexityBridge.UnaryBounded

/-! Charged bit-list parsing of the unary request's nested framing. The
counter measures list-processing calls and Boolean-block inspections; it is
not a Turing-machine runtime or a bound on program validation. -/
namespace Shared.Codes.RequestParseCosts

open Shared.Codes.FiniteProgramBits
open Shared.Codes.BitBlockCosts
open Shared.ComplexityBridge.UnaryBounded
open Shared.ComplexityBridge.CNFWitness

def decodeBoolBlocks : List (List Bool) → Option (List Bool) × Nat
  | [] => (some [],1)
  | [b]::rest =>
      let next := decodeBoolBlocks rest
      (next.1.map (b::·),1+next.2)
  | _::_ => (none,1)

theorem decodeBoolBlocks_correct (blocks : List (List Bool)) :
    (decodeBoolBlocks blocks).1 = blocks.mapM (@BitstringEncoding.bitDecode Bool _) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    cases block with
    | nil =>
      have h : (BitstringEncoding.bitDecode [] : Option Bool) = none := rfl
      simp [decodeBoolBlocks,List.mapM_cons,h]
    | cons b tail =>
      cases tail with
      | nil =>
        have h : (BitstringEncoding.bitDecode [b] : Option Bool) = some b := rfl
        simp [decodeBoolBlocks,List.mapM_cons,h,ih,Option.map_eq_bind]
      | cons c cs =>
        have h : (BitstringEncoding.bitDecode (b::c::cs) : Option Bool) = none := rfl
        simp [decodeBoolBlocks,List.mapM_cons,h]

theorem decodeBoolBlocks_steps (blocks : List (List Bool)) :
    (decodeBoolBlocks blocks).2 ≤ blocks.length+1 := by
  induction blocks with
  | nil => simp [decodeBoolBlocks]
  | cons block rest ih =>
    cases block with
    | nil => simp [decodeBoolBlocks]
    | cons b tail =>
      cases tail with
      | nil => simp only [decodeBoolBlocks,List.length_cons]; omega
      | cons c cs => simp [decodeBoolBlocks]

def boolList (bits : List Bool) : Option (List Bool) × Nat :=
  let framed := parseBlocks bits
  match framed.1 with
  | none => (none,1+framed.2)
  | some blocks =>
      let result := decodeBoolBlocks blocks
      (result.1,1+framed.2+result.2)

theorem boolList_correct (bits : List Bool) :
    (boolList bits).1 = (BitstringEncoding.bitDecode bits : Option (List Bool)) := by
  change (boolList bits).1 = (BitstringEncoding.undelimitBlocks bits).bind (·.mapM BitstringEncoding.bitDecode)
  have h := parseBlocks_correct bits
  cases hp : (parseBlocks bits).1 with
  | none => simp [boolList,hp,←h]
  | some blocks => simp [boolList,hp,←h,decodeBoolBlocks_correct]

theorem boolList_steps (bits : List Bool) : (boolList bits).2 ≤ 3*bits.length+3 := by
  have hp := parseBlocks_steps bits
  cases hb : (parseBlocks bits).1 with
  | none => simp only [boolList,hb]; omega
  | some blocks =>
    have hs : BitstringEncoding.undelimitBlocks bits = some blocks := by rw [←parseBlocks_correct,hb]
    have hl := blocks_length_bound blocks
    rw [blocks_sound bits blocks hs] at hl
    have hd := decodeBoolBlocks_steps blocks
    simp only [boolList,hb]
    omega

/-- Pair framing charges the block parser, both component parsers, and one
dispatch unit. Both components are inspected even if one fails. -/
def pair {α β : Type} (pa : List Bool → Option α × Nat) (pb : List Bool → Option β × Nat)
    (bits : List Bool) : Option (α × β) × Nat :=
  let frame := readBlock bits
  match frame.1 with
  | none => (none,1+frame.2)
  | some (left,right) =>
      let a := pa left
      let b := pb right
      (match a.1,b.1 with | some x,some y => some (x,y) | _,_ => none,
        1+frame.2+a.2+b.2)

theorem pair_correct {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (pa : List Bool → Option α × Nat) (pb : List Bool → Option β × Nat)
    (ha : ∀ bits, (pa bits).1 = BitstringEncoding.bitDecode bits)
    (hb : ∀ bits, (pb bits).1 = BitstringEncoding.bitDecode bits) (bits : List Bool) :
    (pair pa pb bits).1 = (BitstringEncoding.bitDecode bits : Option (α × β)) := by
  change (pair pa pb bits).1 = (match BitstringEncoding.undelimit bits with
    | none => none
    | some (left,right) => match (BitstringEncoding.bitDecode left : Option α),
        (BitstringEncoding.bitDecode right : Option β) with
      | some x,some y => some (x,y) | _,_ => none)
  have hf := readBlock_correct bits
  cases hr : (readBlock bits).1 with
  | none => simp [pair,hr,←hf]
  | some v =>
    rcases v with ⟨left,right⟩
    simp [pair,hr,←hf,ha,hb]

theorem pair_steps {α β : Type} (pa : List Bool → Option α × Nat) (pb : List Bool → Option β × Nat)
    (ca ka cb kb : Nat)
    (ha : ∀ bits, (pa bits).2 ≤ ca*bits.length+ka)
    (hb : ∀ bits, (pb bits).2 ≤ cb*bits.length+kb) (bits : List Bool) :
    (pair pa pb bits).2 ≤ (ca+cb+1)*bits.length+(ka+kb+2) := by
  have hf := readBlock_steps bits
  cases hr : (readBlock bits).1 with
  | none =>
    simp only [pair,hr,Prod.snd]
    have h0 : bits.length ≤ (ca+cb+1)*bits.length := by
      simpa using Nat.mul_le_mul_right bits.length (show 1 ≤ ca+cb+1 by omega)
    omega
  | some v =>
    rcases v with ⟨left,right⟩
    have hs : BitstringEncoding.undelimit bits = some (left,right) := by rw [←readBlock_correct,hr]
    have he := undelimit_sound bits left right hs
    have hlen := congrArg List.length he
    simp only [List.length_append,BitstringEncoding.length_delimit] at hlen
    have hl : left.length ≤ bits.length := by omega
    have hr' : right.length ≤ bits.length := by omega
    have hla := (ha left).trans (Nat.add_le_add_right (Nat.mul_le_mul_left ca hl) ka)
    have hrb := (hb right).trans (Nat.add_le_add_right (Nat.mul_le_mul_left cb hr') kb)
    simp only [pair,hr,Prod.snd]
    rw [Nat.add_mul,Nat.add_mul,one_mul]
    omega

def requestParser (bits : List Bool) : Option Request × Nat :=
  pair (pair boolList boolList) (pair boolList boolList) bits

theorem requestParser_correct (bits : List Bool) : (requestParser bits).1 = parseRequest bits := by
  exact pair_correct _ _ (pair_correct _ _ boolList_correct boolList_correct)
    (pair_correct _ _ boolList_correct boolList_correct) bits

theorem requestParser_steps (bits : List Bool) : (requestParser bits).2 ≤ 15*bits.length+18 := by
  have hp : ∀ b, (pair boolList boolList b).2 ≤ 7*b.length+8 := by
    intro b
    simpa using pair_steps boolList boolList 3 3 3 3 boolList_steps boolList_steps b
  simpa [requestParser] using pair_steps (pair boolList boolList) (pair boolList boolList) 7 8 7 8 hp hp bits

namespace Fixtures
example : (requestParser (request [] [] 0 0)).1 = some ((([],[]),([],[])) : Request) := by decide
example : (requestParser [true]).1 = none := by decide
example : (boolList [true,true,false]).1 = some [true] := by decide
example : (boolList [false]).1 = none := by decide
end Fixtures

end Shared.Codes.RequestParseCosts
