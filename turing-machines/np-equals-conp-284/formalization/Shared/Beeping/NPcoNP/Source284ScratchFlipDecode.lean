import Shared.Beeping.NPcoNP.Source284ScratchFlip

/-! Total executable mathematical decoder for the payload/one scratch
format with a zero/zero terminator. It is not a source-machine interpreter
or an elementary bit-cost proof. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchFlipDecode

open Shared.Beeping.NPcoNP.Source284TableEncode (bit)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def decode (s : Nat) : Option (List Bool) :=
  if s%4 = 0 then some []
  else if 2 ≤ s%4 then (decode (s/4)).map (fun xs => decide (s%2 = 1)::xs)
  else none
termination_by s
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def inspections (s : Nat) : Nat :=
  if s%4 = 0 then 1
  else if 2 ≤ s%4 then 1+inspections (s/4)
  else 1
termination_by s
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem decode_flipped (w : List Bool) (tail : Nat) : decode (flipped w tail) = some w := by
  induction w with
  | nil => simp [flipped,decode]
  | cons b bs ih =>
    cases b <;> simp only [flipped,bit,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
    · rw [decode]
      have hd : (0+2+4*flipped bs tail)/4 = flipped bs tail := by omega
      simp [Nat.add_mod,Nat.mul_mod,hd,ih]
    · rw [decode]
      have hd : (1+2+4*flipped bs tail)/4 = flipped bs tail := by omega
      simp [Nat.add_mod,Nat.mul_mod,hd,ih]

theorem inspections_flipped (w : List Bool) (tail : Nat) :
    inspections (flipped w tail) = w.length+1 := by
  induction w with
  | nil => simp [flipped,inspections]
  | cons b bs ih =>
    cases b <;> simp only [flipped,bit,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,List.length_cons]
    · rw [inspections]
      have hd : (0+2+4*flipped bs tail)/4 = flipped bs tail := by omega
      simp [Nat.add_mod,Nat.mul_mod,hd,ih] <;> omega
    · rw [inspections]
      have hd : (1+2+4*flipped bs tail)/4 = flipped bs tail := by omega
      simp [Nat.add_mod,Nat.mul_mod,hd,ih] <;> omega

theorem flipped_injective (w₁ w₂ : List Bool) (s₁ s₂ : Nat)
    (h : flipped w₁ s₁ = flipped w₂ s₂) : w₁ = w₂ := by
  have hd := congrArg decode h
  rw [decode_flipped,decode_flipped] at hd
  exact Option.some.inj hd

example : decode 0 = some [] := by decide +kernel
example : decode 1 = none := by decide +kernel
example : decode (flipped [true,false,true] 987) = some [true,false,true] := decode_flipped _ _

end Shared.Beeping.NPcoNP.Source284ScratchFlipDecode
