import Shared.Beeping.NPcoNP.Source284WitnessWindow
import Shared.Beeping.NPcoNP.Source284RawWitnessComputable

/-! Effective witness-window data. These are qualitative primitive-recursion
proofs, not a bit-time bound or a source-machine implementation. -/

namespace Shared.Beeping.NPcoNP.Source284WitnessWindow

open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.BinaryAdditionCanonical
open Shared.Beeping.NPcoNP.Source284Parser (frameBits)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)

private theorem canonical_append_true (xs : List Bool) : Canonical (xs ++ [true]) := by
  induction xs with
  | nil => exact Canonical.cons true [] Canonical.nil (by simp)
  | cons b bs ih =>
    apply Canonical.cons b (bs ++ [true]) ih
    simp

/-- Source payloads can be recovered from the numerical parser's sentinel
description, including empty lists and high-zero aliases. -/
theorem payload_via_description (xs : List Bool) :
    payload xs = ((Shared.Beeping.NPcoNP.Source284Parser.description (value xs)).bits.reverse).tail := by
  rw [Shared.Beeping.NPcoNP.Source284RawParse.parse_description_bits,
    canonical_value_bits (canonical_append_true (payload xs).reverse)]
  simp

theorem payload_primrec : Primrec payload := by
  have hv := Shared.Beeping.NPcoNP.Source284RawWitness.value_primrec
  have hd := Shared.Beeping.NPcoNP.Source284Parser.description_primrec.comp hv
  have hb := Shared.ComplexityBridge.CNFEncodingComputability.bits_primrec.comp hd
  have hr := Primrec.list_reverse.comp hb
  have ht := Primrec.list_tail.comp hr
  exact ht.of_eq (fun xs => (payload_via_description xs).symm)

private theorem frame_primrec : Primrec (fun w : List Bool => frameBits w [true]) := by
  have hs : Primrec₂ (fun (_ : List Bool) => fun p : Bool × List Bool =>
      true :: p.1 :: p.2) := by
    exact (Primrec.list_cons.comp (Primrec.const true)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂
  have hf := Primrec.list_foldr (Primrec.id : Primrec (id : List Bool → List Bool))
    (Primrec.const ([false,true] : List Bool)) hs
  apply hf.of_eq
  intro w
  change List.foldr (fun b rest => true :: b :: rest) [false,true] w = frameBits w [true]
  induction w with
  | nil => rfl
  | cons b bs ih => simp [frameBits, ih]

theorem encode_primrec : Primrec encode :=
  Shared.Beeping.NPcoNP.Source284RawWitness.value_primrec.comp frame_primrec

theorem decode_primrec : Primrec₂ decode := by
  have hwidth : Primrec (fun p : Nat × Nat => width p.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) (Primrec.const 2)
  have hpow : Primrec (fun p : Nat × Nat => 2 ^ width p.1) := by
    have hp : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
    exact hp.comp (Primrec.const 2) hwidth
  have hmod : Primrec (fun p : Nat × Nat => p.2 % 2 ^ width p.1) :=
    Primrec.nat_mod.comp Primrec.snd hpow
  have hw : Primrec (fun p : Nat × Nat => payload (p.2 % 2 ^ width p.1).bits) :=
    payload_primrec.comp (Shared.ComplexityBridge.CNFEncodingComputability.bits_primrec.comp hmod)
  have hlen : Primrec (fun p : Nat × Nat => (payload (p.2 % 2 ^ width p.1).bits).length) :=
    Primrec.list_length.comp hw
  exact (Primrec.ite (Primrec.nat_le.comp hlen Primrec.fst)
    (Primrec.option_some.comp hw) (Primrec.const none)).to₂

theorem encode_computable : Computable encode := encode_primrec.to_comp
theorem decode_computable : Computable₂ decode := decode_primrec.to_comp

/-- A primitive-recursive witness predicate yields an effective numerical
check; no claim is made for arbitrary Boolean predicates. -/
theorem check_primrec (limit : Nat) (predicate : List Bool → Bool)
    (hp : Primrec predicate) : Primrec (check limit predicate) := by
  have hd : Primrec (decode limit) := decode_primrec.comp (Primrec.const limit) Primrec.id
  have hy : Primrec₂ (fun (_ : Nat) (w : List Bool) => predicate w) :=
    (hp.comp Primrec.snd).to₂
  have h := Primrec.option_casesOn hd (Primrec.const false) hy
  apply h.of_eq
  intro certificate
  cases hd' : decode limit certificate <;> simp [check, hd']

theorem check_computable (limit : Nat) (predicate : List Bool → Bool)
    (hp : Primrec predicate) : Computable (check limit predicate) :=
  (check_primrec limit predicate hp).to_comp

end Shared.Beeping.NPcoNP.Source284WitnessWindow
