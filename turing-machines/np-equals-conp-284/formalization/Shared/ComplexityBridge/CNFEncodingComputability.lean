import Shared.ComplexityBridge.CNFDisjunctionComputability
import Shared.Codes.VerifierPrograms
import Mathlib.Data.Nat.Bitwise

/-! Computability of the pinned Google bitstring encoding for CNF syntax.
No polynomial-time or bit-cost claim is made here. -/
namespace Shared.ComplexityBridge.CNFEncodingComputability

open Shared.ComplexityBridge.CNF
open Shared.Codes.VerifierPrograms

theorem encodePosNum_bits (p : PosNum) : Computability.encodePosNum p = (p : Nat).bits := by
  induction p with
  | one => simp [Computability.encodePosNum]
  | bit0 p ih =>
    have hn : (p : Nat) ≠ 0 := Nat.ne_of_gt (PosNum.to_nat_pos p)
    rw [Computability.encodePosNum,PosNum.cast_bit0,←two_mul,Nat.bit0_bits _ hn,←ih]
  | bit1 p ih =>
    rw [Computability.encodePosNum,PosNum.cast_bit1,←two_mul,Nat.bit1_bits,←ih]

theorem encodeNat_bits (n : Nat) : Computability.encodeNat n = n.bits := by
  have h (q : Num) : Computability.encodeNum q = (q : Nat).bits := by
    cases q with
    | zero => simp [Computability.encodeNum]
    | pos p => simpa [Computability.encodeNum] using encodePosNum_bits p
  simpa only [Computability.encodeNat,Num.to_of_nat] using h (n : Num)

theorem bits_unfold (n : Nat) (h : n ≠ 0) : n.bits = n.bodd :: n.div2.bits := by
  unfold Nat.bits
  rw [Nat.binaryRec_of_ne_zero _ _ h]
  simp

def bitStep (s : Nat × List Bool) : Nat × List Bool :=
  if s.1 = 0 then s else (s.1.div2,s.1.bodd::s.2)

def bitLoop (fuel : Nat) (s : Nat × List Bool) : Nat × List Bool :=
  bitStep^[fuel] s

theorem bitLoop_correct (fuel n : Nat) (acc : List Bool) (h : n ≤ fuel) :
    bitLoop fuel (n,acc) = (0,n.bits.reverse ++ acc) := by
  induction fuel generalizing n acc with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    simp [bitLoop]
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst n
      simp [bitLoop,bitStep,Function.iterate_fixed]
    · have hd : n.div2 ≤ fuel := by
        have hlt := Nat.binaryRec_decreasing hn
        omega
      rw [bitLoop,Function.iterate_succ_apply,bitStep,if_neg hn]
      change bitLoop fuel (n.div2,n.bodd::acc) = _
      rw [ih n.div2 (n.bodd::acc) hd,bits_unfold n hn]
      simp [List.reverse_cons,List.append_assoc]

theorem bitStep_primrec : Primrec bitStep := by
  have hn : Primrec (fun s : Nat × List Bool => s.1) := Primrec.fst
  have hs : Primrec (fun s : Nat × List Bool => (s.1.div2,s.1.bodd::s.2)) :=
    Primrec.pair (Primrec.nat_div2.comp hn)
      (Primrec.list_cons.comp (Primrec.nat_bodd.comp hn) Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) Primrec.id hs

theorem bits_primrec : Primrec Nat.bits := by
  have hloop : Primrec (fun n : Nat => bitLoop n (n,[])) :=
    Primrec.nat_iterate Primrec.id (Primrec.pair Primrec.id (Primrec.const []))
      (bitStep_primrec.comp Primrec.snd).to₂
  have h := Primrec.list_reverse.comp (Primrec.snd.comp hloop)
  apply h.of_eq
  intro n
  rw [bitLoop_correct n n [] le_rfl]
  simp

theorem natEncoding_primrec : Primrec (@BitstringEncoding.bitEncode Nat _) := by
  apply bits_primrec.of_eq
  intro n
  exact (encodeNat_bits n).symm

theorem pairEncoding_primrec' {α β : Type} [Primcodable α] [Primcodable β]
    [BitstringEncoding α] [BitstringEncoding β]
    (ha : Primrec (@BitstringEncoding.bitEncode α _))
    (hb : Primrec (@BitstringEncoding.bitEncode β _)) :
    Primrec (@BitstringEncoding.bitEncode (α × β) _) := by
  have h := Primrec.list_append.comp (delimit_primrec.comp (ha.comp Primrec.fst)) (hb.comp Primrec.snd)
  exact h.of_eq (fun _ => rfl)

theorem literalEncoding_primrec : Primrec (@BitstringEncoding.bitEncode Literal _) := by
  have h := Primrec.list_append.comp
    (delimit_primrec.comp (natEncoding_primrec.comp Primrec.fst))
    (boolEncoding_primrec.comp Primrec.snd)
  exact h.of_eq (fun _ => rfl)

theorem listEncoding_primrec {α : Type} [Primcodable α] [BitstringEncoding α]
    (hencode : Primrec (@BitstringEncoding.bitEncode α _)) :
    Primrec (@BitstringEncoding.bitEncode (List α) _) := by
  have hmap : Primrec (fun xs : List α => xs.map
      (fun a => BitstringEncoding.delimit (BitstringEncoding.bitEncode a))) :=
    Primrec.list_map Primrec.id (delimit_primrec.comp (hencode.comp Primrec.snd)).to₂
  have h := Primrec.list_flatten.comp hmap
  apply h.of_eq
  intro xs
  change (xs.map (fun a => BitstringEncoding.delimit (BitstringEncoding.bitEncode a))).flatten =
    ((xs.map (fun a => BitstringEncoding.bitEncode a)).map BitstringEncoding.delimit).flatten
  simp only [List.map_map,Function.comp_def]

theorem clauseEncoding_primrec : Primrec (@BitstringEncoding.bitEncode Clause _) :=
  listEncoding_primrec literalEncoding_primrec

theorem formulaEncoding_primrec : Primrec (@BitstringEncoding.bitEncode Formula _) :=
  listEncoding_primrec clauseEncoding_primrec

theorem programEncoding_primrec : Primrec Shared.Codes.FiniteProgramBits.serialize := by
  have hrow : Primrec (@BitstringEncoding.bitEncode Shared.Codes.FinitePrograms.Row _) :=
    pairEncoding_primrec' boolEncoding_primrec
      (pairEncoding_primrec' boolEncoding_primrec (pairEncoding_primrec' natEncoding_primrec natEncoding_primrec))
  exact listEncoding_primrec (pairEncoding_primrec' hrow hrow)

theorem reduction_primrec_of_pair
    (hpair : Primrec (fun z : Shared.ComplexityBridge.UnaryBounded.Decoded =>
      Shared.ComplexityBridge.CircuitPairWitness.pairFormula z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Primrec Shared.ComplexityBridge.UnaryBounded.reduction :=
  Shared.ComplexityBridge.CNFDisjunctionComputability.reduction_primrec_of_pair_and_encoding
    hpair formulaEncoding_primrec

namespace Fixtures
example : Computability.encodeNat 0 = [] := by decide
example : Computability.encodeNat 13 = [true,false,true,true] := by decide
example : bitLoop 13 (13,[]) = (0,[true,true,false,true]) := by decide
end Fixtures

end Shared.ComplexityBridge.CNFEncodingComputability
