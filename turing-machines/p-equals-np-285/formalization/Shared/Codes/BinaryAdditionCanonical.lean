import Shared.Codes.BinaryAddition
import Shared.ComplexityBridge.CNFEncodingComputability

/-! Canonical little-endian numerals have no redundant high zero. -/
namespace Shared.Codes.BinaryAdditionCanonical
open Shared.Codes.BinaryAddition
open Shared.Codes.BitNumeralCompare (value)

inductive Canonical : List Bool → Prop
  | nil : Canonical []
  | cons (b : Bool) (xs : List Bool) : Canonical xs → (xs = [] → b = true) → Canonical (b::xs)

theorem canonical_value_bits {xs : List Bool} (h : Canonical xs) : (value xs).bits = xs := by
  induction h with
  | nil => simp [value]
  | cons b xs hc hz ih =>
    have hh : value xs = 0 → b = true := by
      intro hv
      apply hz
      simpa [hv] using ih.symm
    have he : value (b::xs) = Nat.bit b (value xs) := by
      cases b <;> simp [value,Nat.bit_val]
    rw [he,Nat.bits_append_bit _ _ hh, ih]

theorem value_bits (n : Nat) : value n.bits = n := by
  rw [← Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits]
  exact Shared.Codes.BitNumeralCompare.value_encodeNat n

theorem canonical_bits (n : Nat) : Canonical n.bits := by
  induction n using Nat.binaryRec' with
  | zero => simpa using Canonical.nil
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    apply Canonical.cons b n.bits ih
    intro hn
    apply h
    have hv := congrArg value hn
    simpa [value_bits, value] using hv

theorem value_pos {xs : List Bool} (h : Canonical xs) (hne : xs ≠ []) : 0 < value xs := by
  by_contra hp
  have hz : value xs = 0 := by omega
  have hb := canonical_value_bits h
  rw [hz, Nat.zero_bits] at hb
  exact hne hb.symm

theorem tail_canonical {b : Bool} {xs : List Bool} (h : Canonical (b::xs)) : Canonical xs := by
  cases h with
  | cons _ _ ht _ => exact ht

theorem cons_of_positive (b : Bool) (xs : List Bool) (h : Canonical xs)
    (hp : 0 < value (b::xs)) : Canonical (b::xs) := by
  refine Canonical.cons b xs h ?_
  intro he
  subst xs
  cases b <;> simp_all [value]

theorem addBits_canonical (as bs : List Bool) (c : Bool)
    (ha : Canonical as) (hb : Canonical bs) : Canonical (addBits as bs c) := by
  induction as, bs, c using addBits.induct with
  | case1 => simp [addBits, Canonical.cons, Canonical.nil]
  | case2 c hc =>
    cases c <;> simp_all [addBits, Canonical.nil]
  | case3 a as c ih =>
    rw [addBits]
    apply cons_of_positive _ _ (ih (tail_canonical ha) hb)
    have hp := value_pos ha (by simp)
    simp only [value] at hp
    have hv : 0 < value (addBits (a::as) [] c) := by
      rw [addBits_value]
      simp only [value]
      omega
    rw [addBits] at hv
    exact hv
  | case4 b bs c ih =>
    rw [addBits]
    apply cons_of_positive _ _ (ih ha (tail_canonical hb))
    have hp := value_pos hb (by simp)
    simp only [value] at hp
    have hv : 0 < value (addBits [] (b::bs) c) := by
      rw [addBits_value]
      simp only [value]
      omega
    rw [addBits] at hv
    exact hv
  | case5 a as b bs c ih =>
    rw [addBits]
    apply cons_of_positive _ _ (ih (tail_canonical ha) (tail_canonical hb))
    have hp := value_pos ha (by simp)
    simp only [value] at hp
    have hv : 0 < value (addBits (a::as) (b::bs) c) := by
      rw [addBits_value]
      simp only [value]
      omega
    rw [addBits] at hv
    exact hv

theorem addBits_numerals (a b : Nat) : addBits a.bits b.bits false = (a+b).bits := by
  have hc := addBits_canonical a.bits b.bits false (canonical_bits a) (canonical_bits b)
  have hv := addBits_value a.bits b.bits false
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero, value_bits] at hv
  rw [← hv]
  exact (canonical_value_bits hc).symm

end Shared.Codes.BinaryAdditionCanonical
