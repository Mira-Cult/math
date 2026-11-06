import Shared.Codes.BitProgramLookup

/-! Bit-list witness verifier for unary bounded acceptance. Charges cover
list-processing calls, not instrumentation arithmetic or TM simulation. -/
namespace Shared.Codes.UnaryWitnessVerifier

open Shared.Codes.FinitePrograms
open Shared.Codes.ProgramParseCosts
open Shared.Codes.UnaryRequestValidation
open Shared.Codes.BitTableValidation
open Shared.ComplexityBridge.UnaryBounded

def within : List Bool → List Bool → Bool × Nat
  | [],_ => (true,1)
  | _::_,[] => (false,1)
  | _::xs,_::ys => let r := within xs ys; (r.1,1+r.2)

theorem within_correct (w bound : List Bool) : (within w bound).1 = true ↔ w.length ≤ bound.length := by
  induction w generalizing bound with
  | nil => simp [within]
  | cons b ws ih =>
    cases bound with
    | nil => simp [within]
    | cons c bs => simpa [within] using ih bs

theorem within_steps (w bound : List Bool) : (within w bound).2 ≤ w.length+1 := by
  induction w generalizing bound with
  | nil => simp [within]
  | cons b ws ih =>
    cases bound with
    | nil => simp [within]
    | cons c bs => have h := ih bs; simp only [within,List.length_cons]; omega

def boolListEncode : List Bool → List Bool × Nat
  | [] => ([],1)
  | b::bs => let r := boolListEncode bs; (true::b::false::r.1,1+r.2)

theorem boolListEncode_correct (bits : List Bool) : (boolListEncode bits).1 = BitstringEncoding.bitEncode bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    change true::b::false::(boolListEncode bs).1 = _
    rw [ih]
    rfl

theorem boolListEncode_steps (bits : List Bool) : (boolListEncode bits).2 = bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [boolListEncode,ih,Nat.add_comm]

def delimitEncode : List Bool → List Bool × Nat
  | [] => ([false],1)
  | b::bs => let r := delimitEncode bs; (true::b::r.1,1+r.2)

theorem delimitEncode_correct (bits : List Bool) : (delimitEncode bits).1 = BitstringEncoding.delimit bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [delimitEncode,BitstringEncoding.delimit,ih]

theorem delimitEncode_steps (bits : List Bool) : (delimitEncode bits).2 = bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [delimitEncode,ih,Nat.add_comm]

def appendBits : List Bool → List Bool → List Bool × Nat
  | [],ys => (ys,1)
  | b::bs,ys => let r := appendBits bs ys; (b::r.1,1+r.2)

theorem appendBits_correct (xs ys : List Bool) : (appendBits xs ys).1 = xs++ys := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [appendBits,ih]

theorem appendBits_steps (xs ys : List Bool) : (appendBits xs ys).2 = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [appendBits,ih,Nat.add_comm]

def encodePair (x w : List Bool) : List Bool × Nat :=
  let a := boolListEncode x
  let b := boolListEncode w
  let framed := delimitEncode a.1
  let result := appendBits framed.1 b.1
  (result.1,1+a.2+b.2+framed.2+result.2)

theorem encodePair_correct (x w : List Bool) : (encodePair x w).1 = BitstringEncoding.bitEncode (x,w) := by
  simp only [encodePair,appendBits_correct,delimitEncode_correct,boolListEncode_correct]
  rfl

theorem encodePair_steps (x w : List Bool) : (encodePair x w).2 = 10*x.length+w.length+6 := by
  simp only [encodePair,appendBits_steps,delimitEncode_steps,boolListEncode_steps,
    delimitEncode_correct,boolListEncode_correct,BitstringEncoding.length_delimit,
    Shared.ComplexityBridge.bitstring_list_encoded_length]
  omega

def verifyDecoded (d : BitDecoded) (w : List Bool) : Bool × Nat :=
  let limit := within w d.2.2.1
  if limit.1 then
    let encoded := encodePair d.2.1 w
    let result := Shared.Codes.BitProgramLookup.run d.1
      (Shared.Codes.BitProgramLookup.initial encoded.1) d.2.2.2
    (match result.1 with | some (.inl true) => true | _ => false,
      1+limit.2+encoded.2+result.2)
  else (false,1+limit.2)

theorem verifyDecoded_correct (d : BitDecoded) (w : List Bool) :
    (verifyDecoded d w).1 = true ↔
      w.length ≤ d.2.2.1.length ∧
        FinitePrograms.bounded (interpretProgram d.1) (BitstringEncoding.bitEncode (d.2.1,w)) d.2.2.2.length = some true := by
  have hw := within_correct w d.2.2.1
  have hr := Shared.Codes.BitProgramLookup.bounded_correct d.1 (BitstringEncoding.bitEncode (d.2.1,w)) d.2.2.2
  cases hwithin : (within w d.2.2.1).1 with
  | false =>
    have hn : ¬w.length ≤ d.2.2.1.length := by intro h; have hh := hw.mpr h; rw [hwithin] at hh; contradiction
    simp [verifyDecoded,hwithin,hn]
  | true =>
    have hn : w.length ≤ d.2.2.1.length := hw.mp hwithin
    simp only [verifyDecoded,hwithin,↓reduceIte,encodePair_correct]
    rw [←hr]
    unfold Shared.Codes.BitProgramLookup.bounded
    cases hs : (Shared.Codes.BitProgramLookup.run d.1
        (Shared.Codes.BitProgramLookup.initial (BitstringEncoding.bitEncode (d.2.1,w))) d.2.2.2).1 with
    | none => simp [hs,hn]
    | some s => cases s with
      | inl b => cases b <;> simp [hs,hn]
      | inr c => simp [hs,hn]

def verify (raw w : List Bool) : Bool × Nat :=
  let parsed := decodeBitRequest raw
  match parsed.1 with
  | none => (false,1+parsed.2)
  | some d => let r := verifyDecoded d w; (r.1,1+parsed.2+r.2)

/-- The verifier searches no witnesses itself; acceptance of the independent
reference is exactly existential acceptance by this bounded verifier. -/
theorem accept_iff_exists_verify (raw : List Bool) :
    accept raw = true ↔ ∃ w, (verify raw w).1 = true := by
  have hd := decodeBitRequest_correct raw
  cases hp : (decodeBitRequest raw).1 with
  | none =>
    have hr : decodeRequest raw = none := by rw [←hd,hp]; rfl
    simp [accept,hr,verify,hp]
  | some d =>
    have hr : decodeRequest raw = some (interpretDecoded d) := by rw [←hd,hp]; rfl
    simp only [accept,hr,List.any_eq_true,beq_iff_eq,
      Shared.Codes.VerifierPrograms.mem_witnesses_iff]
    simp only [verify,hp,verifyDecoded_correct,interpretDecoded]

theorem decoded_provenance (raw : List Bool) (d : BitDecoded)
    (h : (decodeBitRequest raw).1 = some d) :
    ∃ description, (parseAndCheck description).1 = some d.1 ∧ description.length ≤ raw.length ∧
      d.2.1.length ≤ raw.length ∧ d.2.2.1.length ≤ raw.length ∧ d.2.2.2.length ≤ raw.length := by
  cases hr : (Shared.Codes.RequestParseCosts.requestParser raw).1 with
  | none => simp [decodeBitRequest,hr] at h
  | some r =>
    have hreq : parseRequest raw = some r := by rw [←Shared.Codes.RequestParseCosts.requestParser_correct,hr]
    have hl := parseRequest_lengths raw r hreq
    cases hp : (parseAndCheck r.1.1).1 with
    | none => simp [decodeBitRequest,hr,hp] at h
    | some p =>
      cases hb : (unaryCheck r.2.1).1 <;> cases hf : (unaryCheck r.2.2).1 <;>
        simp [decodeBitRequest,hr,hp,hb,hf] at h
      subst d
      exact ⟨r.1.1,hp,hl.1,hl.2.1,hl.2.2.1,hl.2.2.2⟩

theorem verifyDecoded_steps (d : BitDecoded) (w description : List Bool)
    (h : (parseAndCheck description).1 = some d.1) :
    (verifyDecoded d w).2 ≤ 1+(w.length+1)+(10*d.2.1.length+w.length+6)+
      (1+d.2.2.2.length*((description.length+1)*(3*description.length+10)+7*description.length+37)) := by
  have hl := within_steps w d.2.2.1
  have he := encodePair_steps d.2.1 w
  have hr := Shared.Codes.BitProgramLookup.validated_run_steps description d.1 (encodePair d.2.1 w).1 d.2.2.2 h
  cases hb : (within w d.2.2.1).1 <;> simp only [verifyDecoded,hb,Bool.false_eq_true,↓reduceIte] <;> omega

theorem verify_steps (raw w : List Bool) :
    (verify raw w).2 ≤ (raw.length+1)*(raw.length+1)+2*raw.length*raw.length+
      raw.length*((raw.length+1)*(3*raw.length+10)+7*raw.length+37)+
      124*raw.length+2*w.length+45 := by
  have hp := decodeBitRequest_steps raw
  cases hd : (decodeBitRequest raw).1 with
  | none => simp only [verify,hd]; omega
  | some d =>
    obtain ⟨description,hdesc,hlen,hx,hbound,hfuel⟩ := decoded_provenance raw d hd
    have hv := verifyDecoded_steps d w description hdesc
    have hm : (description.length+1)*(3*description.length+10) ≤
        (raw.length+1)*(3*raw.length+10) := Nat.mul_le_mul (by omega) (by omega)
    have hbudget : (description.length+1)*(3*description.length+10)+7*description.length+37 ≤
        (raw.length+1)*(3*raw.length+10)+7*raw.length+37 := by omega
    have hrun := Nat.mul_le_mul hfuel hbudget
    simp only [verify,hd]
    omega

theorem verify_witness_length (raw w : List Bool) (h : (verify raw w).1 = true) :
    w.length ≤ raw.length := by
  cases hd : (decodeBitRequest raw).1 with
  | none => simp [verify,hd] at h
  | some d =>
    have hv : (verifyDecoded d w).1 = true := by simpa [verify,hd] using h
    have hlimit := (verifyDecoded_correct d w).mp hv
    obtain ⟨description,hdesc,hlen,hx,hbound,hfuel⟩ := decoded_provenance raw d hd
    exact hlimit.1.trans hbound

theorem accept_iff_bounded_verify (raw : List Bool) :
    accept raw = true ↔ ∃ w, w.length ≤ raw.length ∧ (verify raw w).1 = true := by
  rw [accept_iff_exists_verify]
  constructor
  · rintro ⟨w,h⟩
    exact ⟨w,verify_witness_length raw w h,h⟩
  · rintro ⟨w,_,h⟩
    exact ⟨w,h⟩

namespace Fixtures
example : (verify [true] []).1 = false := by decide
example : (within [true] []).1 = false := by decide
example : (encodePair [] []).1 = [false] := by decide
end Fixtures

end Shared.Codes.UnaryWitnessVerifier
