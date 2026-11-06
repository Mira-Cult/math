import Shared.Beeping.NPcoNP.Source284RawWitness
import Shared.Beeping.NPcoNP.Source284RelativeComputable

/-! Qualitative computability of the guarded raw-list verifier. This does
not provide a polynomial bit-cost bound or a canonical TM2 time bound. -/
namespace Shared.Beeping.NPcoNP.Source284RawWitness

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative

theorem value_primrec : Primrec value := by
  have hstep : Primrec₂ (fun (_ : List Bool) => fun p : Bool × Nat =>
      2 * p.2 + (if p.1 then 1 else 0)) := by
    have hmul : Primrec (fun p : List Bool × (Bool × Nat) => 2 * p.2.2) :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)
    have hbit : Primrec (fun p : List Bool × (Bool × Nat) => if p.2.1 then 1 else 0) := by
      have hb : Primrec (fun p : List Bool × (Bool × Nat) => bif p.2.1 then (1 : Nat) else 0) :=
        Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0)
      apply hb.of_eq
      intro p
      cases p.2.1 <;> rfl
    exact (Primrec.nat_add.comp hmul hbit).to₂
  have hf := Primrec.list_foldr (Primrec.id : Primrec (id : List Bool → List Bool))
    (Primrec.const (0 : Nat)) hstep
  apply hf.of_eq
  intro xs
  change List.foldr (fun b s => 2 * s + if b then 1 else 0) 0 xs = value xs
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [value, ih]

theorem checker_primrec : Primrec checker := by
  have hi : Primrec (fun p : List Bool × List Bool => value p.1) :=
    value_primrec.comp Primrec.fst
  have hw : Primrec (fun p : List Bool × List Bool => value p.2) :=
    value_primrec.comp Primrec.snd
  have hn : Primrec (fun p : List Bool × List Bool => Source284Parser.length (value p.1)) :=
    Source284Parser.length_primrec.comp hi
  have hd : Primrec (fun p : List Bool × List Bool => Source284Parser.description (value p.1)) :=
    Source284Parser.description_primrec.comp hi
  have hlen : Primrec (fun p : List Bool × List Bool => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have ha : Primrec (fun p : List Bool × List Bool =>
      accepts (Source284Parser.description (value p.1)) 0 (value p.2)
        (Source284Parser.length (value p.1))) := by
    exact boundedAttempt_primrec.comp (Primrec.pair (Primrec.pair hd (Primrec.const 0))
      (Primrec.pair hw hn))
  exact Primrec.ite (Primrec.nat_le.comp hlen hn) ha (Primrec.const false)

theorem checker_computable : Computable checker := checker_primrec.to_comp

end Shared.Beeping.NPcoNP.Source284RawWitness
