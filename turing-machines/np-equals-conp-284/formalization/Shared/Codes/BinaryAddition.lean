import Shared.Codes.BitTableValidation
set_option maxHeartbeats 3000000

/-! Little-endian bit-list addition for finite machine implementations. Raw
lists may contain high zero bits; the value theorem covers them as supplied. -/
namespace Shared.Codes.BinaryAddition
open Shared.Codes.BitNumeralCompare (value)

def sumBit (a b carry : Bool) : Bool := xor (xor a b) carry
def carryBit (a b carry : Bool) : Bool := (a && b) || (a && carry) || (b && carry)

def addBits : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | a::as, [], c => sumBit a false c :: addBits as [] (carryBit a false c)
  | [], b::bs, c => sumBit false b c :: addBits [] bs (carryBit false b c)
  | a::as, b::bs, c => sumBit a b c :: addBits as bs (carryBit a b c)
termination_by as bs _ => as.length+bs.length

theorem digit_value (a b c : Bool) :
    (if sumBit a b c then 1 else 0) + 2*(if carryBit a b c then 1 else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

/-- The ripple circuit computes the sum, including a supplied carry bit. -/
theorem addBits_value (as bs : List Bool) (c : Bool) :
    value (addBits as bs c) = value as + value bs + (if c then 1 else 0) := by
  induction as, bs, c using addBits.induct with
  | case1 => simp [addBits,value]
  | case2 c hc => cases c <;> simp_all [addBits,value]
  | case3 a as c ih =>
    simp only [addBits,value,ih]
    have h := digit_value a false c
    simp only [Bool.false_eq_true,ite_false] at h
    omega
  | case4 b bs c ih =>
    simp only [addBits,value,ih]
    have h := digit_value false b c
    simp only [Bool.false_eq_true,ite_false] at h
    omega
  | case5 a as b bs c ih =>
    simp only [addBits,value,ih]
    have h := digit_value a b c
    omega

/-- At most one carry bit extends the longer input. -/
theorem addBits_length (as bs : List Bool) (c : Bool) :
    (addBits as bs c).length ≤ max as.length bs.length+1 := by
  induction as, bs, c using addBits.induct with
  | case1 => simp [addBits]
  | case2 c hc => cases c <;> simp_all [addBits]
  | case3 a as c ih => simp [addBits] at *; omega
  | case4 b bs c ih => simp [addBits] at *; omega
  | case5 a as b bs c ih =>
    simp only [addBits,List.length_cons] at *
    have hm : max (as.length+1) (bs.length+1) = max as.length bs.length+1 := by omega
    rw [hm]
    omega

namespace Fixtures
example : addBits [true,true] [true] false = [false,false,true] := by simp [addBits,sumBit,carryBit]
example : addBits [] [] false = [] := by simp [addBits]
example : addBits [] [] true = [true] := by simp [addBits]
end Fixtures
end Shared.Codes.BinaryAddition
