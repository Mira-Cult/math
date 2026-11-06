import Shared.Codes.FiniteProgramBits

/-! Charged bit-list parsing of the pinned self-delimiting block stream.
The counter charges one unit per block-stream call and one per `readBlock`
call. Each `readBlock` call inspects at most two input bits and creates at
most one payload cons cell. This is a list-operation bound, not yet a
Turing-machine simulation or a bound for the complete program decoder. -/
namespace Shared.Codes.BitBlockCosts

open Shared.Codes.FiniteProgramBits

theorem readBlock_success_steps (bits payload rest : List Bool)
    (h : (readBlock bits).1 = some (payload,rest)) :
    (readBlock bits).2 + rest.length ≤ bits.length := by
  induction bits using readBlock.induct generalizing payload rest with
  | case1 => simp [readBlock] at h
  | case2 xs =>
    simp only [readBlock,Prod.fst,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simp [readBlock] <;> omega
  | case3 => simp [readBlock] at h
  | case4 b xs ih =>
    cases hr : (readBlock xs).1 with
    | none => simp [readBlock,hr] at h
    | some v =>
      rcases v with ⟨p,r⟩
      simp only [readBlock,Prod.fst,hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hh := ih p r hr
      simp only [readBlock,Prod.snd,List.length_cons]
      omega

/-- A costed implementation of the library's fuel-bounded block parser. -/
def readBlocks : Nat → List Bool → Option (List (List Bool)) × Nat
  | _, [] => (some [],1)
  | 0, _::_ => (none,1)
  | fuel+1, b::bs =>
      let r := readBlock (b::bs)
      match r.1 with
      | none => (none,1+r.2)
      | some (payload,rest) =>
          let next := readBlocks fuel rest
          (next.1.map (payload::·),1+r.2+next.2)

theorem readBlocks_correct (fuel : Nat) (bits : List Bool) :
    (readBlocks fuel bits).1 = BitstringEncoding.undelimitBlocksAux fuel bits := by
  induction fuel generalizing bits with
  | zero => cases bits <;> rfl
  | succ fuel ih =>
    cases bits with
    | nil => rfl
    | cons b bs =>
      have hblock := readBlock_correct (b::bs)
      cases hr : (readBlock (b::bs)).1 with
      | none => simp [readBlocks,BitstringEncoding.undelimitBlocksAux,←hblock,hr]
      | some v =>
        rcases v with ⟨payload,rest⟩
        simp [readBlocks,BitstringEncoding.undelimitBlocksAux,←hblock,hr,ih]

/-- The charged block-stream operations are linear in the supplied raw
bit length, independently of the fuel. -/
theorem readBlocks_steps (fuel : Nat) (bits : List Bool) :
    (readBlocks fuel bits).2 ≤ 2*bits.length+1 := by
  induction fuel generalizing bits with
  | zero => cases bits <;> simp [readBlocks]
  | succ fuel ih =>
    cases bits with
    | nil => simp [readBlocks]
    | cons b bs =>
      have hcost := readBlock_steps (b::bs)
      cases hr : (readBlock (b::bs)).1 with
      | none =>
        simp only [readBlocks,hr,Prod.snd,List.length_cons]
        simp only [List.length_cons] at hcost
        omega
      | some v =>
        rcases v with ⟨payload,rest⟩
        have hspent := readBlock_success_steps (b::bs) payload rest hr
        have hpositive : 0 < (readBlock (b::bs)).2 := by
          cases b <;> cases bs <;> simp [readBlock]
        have hrest : rest.length < (b::bs).length := by omega
        have hnext := ih rest
        simp only [readBlocks,hr,Prod.snd,List.length_cons]
        simp only [List.length_cons] at hspent hrest
        omega

def parseBlocks (bits : List Bool) : Option (List (List Bool)) × Nat := readBlocks bits.length bits

theorem parseBlocks_correct (bits : List Bool) :
    (parseBlocks bits).1 = BitstringEncoding.undelimitBlocks bits := readBlocks_correct bits.length bits

theorem parseBlocks_steps (bits : List Bool) : (parseBlocks bits).2 ≤ 2*bits.length+1 :=
  readBlocks_steps bits.length bits

namespace Fixtures
example : parseBlocks [] = (some [],1) := by decide
example : (parseBlocks [false,true,true,false]).1 = some [[],[true]] := by decide
example : (parseBlocks [true]).1 = none := by decide
end Fixtures

end Shared.Codes.BitBlockCosts
