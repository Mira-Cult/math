import Shared.Codes.BitTableValidation

/-! Charged bit-list request parsing and validation for unary bounded
acceptance. All program numbers remain raw bit lists, and unary bounds remain
unary lists. Counter arithmetic and Turing-machine simulation are not charged. -/
namespace Shared.Codes.UnaryRequestValidation

open Shared.Codes.FiniteProgramBits
open Shared.Codes.ProgramParseCosts
open Shared.Codes.RequestParseCosts
open Shared.Codes.BitTableValidation
open Shared.ComplexityBridge.UnaryBounded

def unaryCheck : List Bool → Bool × Nat
  | [] => (true,1)
  | b::bs => let r := unaryCheck bs; (b && r.1,1+r.2)

theorem unaryCheck_correct (bits : List Bool) : (unaryCheck bits).1 = bits.all id := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [unaryCheck,ih]

theorem unaryCheck_steps (bits : List Bool) : (unaryCheck bits).2 = bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [unaryCheck,ih,Nat.add_comm]

abbrev BitDecoded := BitProgram × List Bool × List Bool × List Bool

def interpretDecoded (d : BitDecoded) : Decoded :=
  (interpretProgram d.1,d.2.1,d.2.2.1.length,d.2.2.2.length)

/-- The input and unary clocks remain lists; `interpretDecoded` is a semantic
view, not a runtime conversion into unbounded integers. -/
def decodeBitRequest (raw : List Bool) : Option BitDecoded × Nat :=
  let parsed := requestParser raw
  match parsed.1 with
  | none => (none,1+parsed.2)
  | some r =>
      let program := parseAndCheck r.1.1
      let bound := unaryCheck r.2.1
      let fuel := unaryCheck r.2.2
      (match program.1 with
       | none => none
       | some p => if bound.1 && fuel.1 then some (p,r.1.2,r.2.1,r.2.2) else none,
       1+parsed.2+program.2+bound.2+fuel.2)

theorem decodeBitRequest_correct (raw : List Bool) :
    (decodeBitRequest raw).1.map interpretDecoded = decodeRequest raw := by
  have hparse := requestParser_correct raw
  cases hr : (requestParser raw).1 with
  | none =>
    have hreq : parseRequest raw = none := by rw [←hparse,hr]
    simp [decodeBitRequest,hr,decodeRequest,hreq]
  | some r =>
    have hreq : parseRequest raw = some r := by rw [←hparse,hr]
    have hp := parseAndCheck_correct r.1.1
    cases hv : (parseAndCheck r.1.1).1 with
    | none =>
      have hvalid : parseValid r.1.1 = none := by rw [←hp,hv]; rfl
      simp [decodeBitRequest,hr,hv,decodeRequest,decodeFields,hreq,hvalid]
    | some p =>
      have hvalid : parseValid r.1.1 = some (interpretProgram p) := by rw [←hp,hv]; rfl
      have hb := unaryCheck_correct r.2.1
      have hf := unaryCheck_correct r.2.2
      cases hbound : (unaryCheck r.2.1).1 <;> cases hfuel : (unaryCheck r.2.2).1 <;>
        simp [decodeBitRequest,hr,hv,decodeRequest,decodeFields,hreq,hvalid,unaryValue,←hb,←hf,hbound,hfuel,interpretDecoded]

theorem decodeBitRequest_steps (raw : List Bool) :
    (decodeBitRequest raw).2 ≤ (raw.length+1)*(raw.length+1)+
      2*raw.length*raw.length+114*raw.length+30 := by
  have hp := requestParser_steps raw
  cases hr : (requestParser raw).1 with
  | none =>
    simp only [decodeBitRequest,hr]
    omega
  | some r =>
    have hreq : parseRequest raw = some r := by rw [←requestParser_correct,hr]
    have hl := parseRequest_lengths raw r hreq
    have hc := parseAndCheck_steps r.1.1
    have hb := unaryCheck_steps r.2.1
    have hf := unaryCheck_steps r.2.2
    have hn : r.1.1.length ≤ raw.length := hl.1
    have hsquare : (r.1.1.length+1)*(r.1.1.length+1) ≤ (raw.length+1)*(raw.length+1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hmul : r.1.1.length*r.1.1.length ≤ raw.length*raw.length := Nat.mul_le_mul hn hn
    have hmul2 : 2*r.1.1.length*r.1.1.length ≤ 2*raw.length*raw.length := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hmul
    cases hv : (parseAndCheck r.1.1).1 <;>
      simp only [decodeBitRequest,hr,hv,Prod.snd] <;> omega

namespace Fixtures
example : (decodeBitRequest [true]).1 = none := by decide
example : (unaryCheck []).1 = true := by decide
example : (unaryCheck [true,false]).1 = false := by decide
example (p : Shared.Codes.FinitePrograms.Program) (x : List Bool) (bound fuel : Nat)
    (h : Shared.Codes.FinitePrograms.valid p = true) :
    (decodeBitRequest (request (serialize p) x bound fuel)).1.map interpretDecoded = some (p,x,bound,fuel) := by
  rw [decodeBitRequest_correct,decode_request p x bound fuel h]
end Fixtures

end Shared.Codes.UnaryRequestValidation
