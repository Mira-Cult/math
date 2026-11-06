import Shared.Codes.ProgramParseCosts
import Shared.ComplexityBridge.NumeralNormalization

/-! Comparison of the pinned raw binary numeral payloads, including accepted
noncanonical encodings. The cost counts recursive bit-list inspections, not
a complete Turing-machine simulation. -/
namespace Shared.Codes.BitNumeralCompare

open Shared.ComplexityBridge.NumeralNormalization

def value : List Bool → Nat
  | [] => 0
  | b::bs => 2*value bs + if b then 1 else 0

theorem value_encodePosNum (p : PosNum) : value (Computability.encodePosNum p) = (p : Nat) := by
  induction p with
  | one => rfl
  | bit0 p ih => simp [Computability.encodePosNum,value,PosNum.cast_bit0,ih]; omega
  | bit1 p ih => simp [Computability.encodePosNum,value,PosNum.cast_bit1,ih]; omega

theorem value_encodeNat (n : Nat) : value (Computability.encodeNat n) = n := by
  have h (q : Num) : value (Computability.encodeNum q) = (q : Nat) := by
    cases q with
    | zero => rfl
    | pos p => simpa [Computability.encodeNum] using value_encodePosNum p
  simpa only [Computability.encodeNat,Num.to_of_nat] using h (n : Num)

theorem value_normalize (bits : List Bool) : value (normalize bits) = Computability.decodeNat bits := by
  rw [←encode_decode_nat,value_encodeNat]

/-- More significant bits are inspected recursively; they override a
disagreement at a less significant position. Missing bits are zero. -/
def compareBits : List Bool → List Bool → Ordering
  | [],[] => .eq
  | a::as,[] =>
      match compareBits as [] with
      | .eq => if a then .gt else .eq
      | o => o
  | [],b::bs =>
      match compareBits [] bs with
      | .eq => if b then .lt else .eq
      | o => o
  | a::as,b::bs =>
      match compareBits as bs with
      | .eq => if a == b then .eq else if a then .gt else .lt
      | o => o
termination_by xs ys => xs.length+ys.length

theorem compare_digit (x y : Nat) (a b : Bool) :
    (match compare x y with
      | .eq => if a == b then .eq else if a then .gt else .lt
      | o => o) = compare (2*x + if a then 1 else 0) (2*y + if b then 1 else 0) := by
  cases h : compare x y <;> cases a <;> cases b
  all_goals simp only [compare_eq_iff_eq,compare_lt_iff_lt,compare_gt_iff_gt] at h
  all_goals simp only [h,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,Bool.true_eq_false]
  all_goals symm
  all_goals first | apply compare_eq_iff_eq.mpr | apply compare_lt_iff_lt.mpr | apply compare_gt_iff_gt.mpr
  all_goals omega

theorem compareBits_correct (xs ys : List Bool) : compareBits xs ys = compare (value xs) (value ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [compareBits,value,compare_eq_iff_eq]
    | cons b bs ih =>
      rw [compareBits,ih]
      have h := compare_digit 0 (value bs) false b
      cases b <;> simpa [value] using h
  | cons a as ih =>
    cases ys with
    | nil =>
      rw [compareBits,ih []]
      have h := compare_digit (value as) 0 a false
      cases a <;> simpa [value] using h
    | cons b bs =>
      rw [compareBits,ih bs]
      exact compare_digit (value as) (value bs) a b

def positiveCost : List Bool → List Bool × Nat
  | [] => ([true],1)
  | b::bs =>
      if b && bs.isEmpty then ([true],1) else
        let r := positiveCost bs
        (b::r.1,1+r.2)

theorem positiveCost_correct (xs : List Bool) : (positiveCost xs).1 = normalizePositive xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> rfl
    | cons c cs =>
      cases b <;>
        change _::(positiveCost (c::cs)).1 = _::normalizePositive (c::cs) <;>
        rw [ih]

theorem positiveCost_steps (xs : List Bool) : (positiveCost xs).2 ≤ xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> cases bs <;> simp [positiveCost] at * <;> omega

def normalizeCost (bits : List Bool) : List Bool × Nat :=
  match bits with
  | [] => ([],1)
  | _::_ => let r := positiveCost bits; (r.1,1+r.2)

theorem normalizeCost_correct (bits : List Bool) : (normalizeCost bits).1 = normalize bits := by
  cases bits with
  | nil => rfl
  | cons b bs => simpa [normalizeCost,positiveCost_correct] using (normalize_eq_positive (b::bs) (by simp)).symm

theorem normalizeCost_steps (bits : List Bool) : (normalizeCost bits).2 ≤ bits.length+2 := by
  cases bits with
  | nil => simp [normalizeCost]
  | cons b bs =>
    have h := positiveCost_steps (b::bs)
    simp only [normalizeCost,List.length_cons] at *
    omega

def compareCost : List Bool → List Bool → Ordering × Nat
  | [],[] => (.eq,1)
  | a::as,[] =>
      let r := compareCost as []
      (match r.1 with | .eq => if a then .gt else .eq | o => o, 1+r.2)
  | [],b::bs =>
      let r := compareCost [] bs
      (match r.1 with | .eq => if b then .lt else .eq | o => o, 1+r.2)
  | a::as,b::bs =>
      let r := compareCost as bs
      (match r.1 with | .eq => if a == b then .eq else if a then .gt else .lt | o => o, 1+r.2)
termination_by xs ys => xs.length+ys.length

theorem compareCost_correct (xs ys : List Bool) : (compareCost xs ys).1 = compareBits xs ys := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [compareCost,compareBits]
    | cons b bs ih => simp only [compareCost,compareBits]; rw [ih]
  | cons a as ih =>
    cases ys with
    | nil => simp only [compareCost,compareBits]; rw [ih []]
    | cons b bs => simp only [compareCost,compareBits]; rw [ih bs]

theorem compareCost_steps (xs ys : List Bool) : (compareCost xs ys).2 ≤ xs.length+ys.length+1 := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [compareCost]
    | cons b bs ih => simp only [List.length_nil] at ih; simp only [compareCost,List.length_nil,List.length_cons]; omega
  | cons a as ih =>
    cases ys with
    | nil => have h := ih []; simp only [compareCost,List.length_nil,List.length_cons] at *; omega
    | cons b bs => have h := ih bs; simp only [compareCost,List.length_cons] at *; omega

def compareRawCost (xs ys : List Bool) : Ordering × Nat :=
  let a := normalizeCost xs
  let b := normalizeCost ys
  let c := compareCost a.1 b.1
  (c.1,1+a.2+b.2+c.2)

theorem compareRawCost_correct (xs ys : List Bool) :
    (compareRawCost xs ys).1 = compare (Computability.decodeNat xs) (Computability.decodeNat ys) := by
  simp only [compareRawCost,compareCost_correct,normalizeCost_correct,compareBits_correct,value_normalize]

theorem compareRawCost_lt (xs ys : List Bool) :
    (compareRawCost xs ys).1 = .lt ↔ Computability.decodeNat xs < Computability.decodeNat ys := by
  rw [compareRawCost_correct,compare_lt_iff_lt]

theorem compareRawCost_eq (xs ys : List Bool) :
    (compareRawCost xs ys).1 = .eq ↔ Computability.decodeNat xs = Computability.decodeNat ys := by
  rw [compareRawCost_correct,compare_eq_iff_eq]

theorem compareRawCost_steps (xs ys : List Bool) :
    (compareRawCost xs ys).2 ≤ 2*xs.length+2*ys.length+8 := by
  have hx := normalizeCost_steps xs
  have hy := normalizeCost_steps ys
  have hc := compareCost_steps (normalizeCost xs).1 (normalizeCost ys).1
  have hlx : (normalizeCost xs).1.length ≤ xs.length+1 := by rw [normalizeCost_correct]; exact normalize_length xs
  have hly : (normalizeCost ys).1.length ≤ ys.length+1 := by rw [normalizeCost_correct]; exact normalize_length ys
  simp only [compareRawCost]
  omega

namespace Fixtures
example : (compareRawCost [false] [false,true]).1 = .eq := by rw [compareRawCost_correct]; decide
example : (compareRawCost [] [false]).1 = .lt := by rw [compareRawCost_correct]; decide
example : (compareRawCost [false] [true]).1 = .gt := by rw [compareRawCost_correct]; decide
end Fixtures

end Shared.Codes.BitNumeralCompare
