import Shared.ComplexityBridge.CNFWitness

namespace Shared.ComplexityBridge.NumeralNormalization

/-- The last raw bit encountered, with an explicit empty-input case. -/
def lastSeen : List Bool → Option Bool → Option Bool
  | [], old => old
  | b::xs, _ => lastSeen xs (some b)

/-- Append the implicit most-significant one precisely when a nonempty raw
encoding ends in zero. The empty encoding remains zero. -/
def normalize (xs : List Bool) : List Bool :=
  xs ++ if lastSeen xs none = some false then [true] else []

/-- A structurally recursive presentation convenient for the pinned positive
binary decoder. -/
def normalizePositive : List Bool → List Bool
  | [] => [true]
  | [true] => [true]
  | b::xs => b::normalizePositive xs

theorem lastSeen_nonempty (xs : List Bool) (h : xs ≠ []) (a b : Option Bool) :
    lastSeen xs a = lastSeen xs b := by
  cases xs with
  | nil => contradiction
  | cons c xs => rfl

set_option backward.isDefEq.respectTransparency false in
theorem normalize_cons_nonempty (b : Bool) (xs : List Bool) (h : xs ≠ []) :
    normalize (b::xs) = b::normalize xs := by
  cases xs with
  | nil => contradiction
  | cons c xs => rfl

theorem normalize_eq_positive (xs : List Bool) (h : xs ≠ []) : normalize xs = normalizePositive xs := by
  induction xs with
  | nil => contradiction
  | cons b xs ih =>
    cases xs with
    | nil => cases b <;> rfl
    | cons c xs =>
      rw [normalize_cons_nonempty b (c::xs) (by simp),ih (by simp)]
      cases b <;> rfl

/-- The finite bit normalization is exactly mathlib's canonical positive
encoding of the actual decoded binary number. -/
theorem encode_decode_positive (xs : List Bool) :
    Computability.encodePosNum (Computability.decodePosNum xs) = normalizePositive xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => simp [Computability.decodePosNum,Computability.encodePosNum,normalizePositive,ih]
    | true =>
      cases xs with
      | nil => rfl
      | cons c xs => simp [Computability.decodePosNum,Computability.encodePosNum,normalizePositive,ih]

/-- Correctness for the public natural-number decoder, including zero. -/
theorem encode_decode_nat (xs : List Bool) :
    Computability.encodeNat (Computability.decodeNat xs) = normalize xs := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    have he : Computability.decodeNat (b::xs) = ((Num.pos (Computability.decodePosNum (b::xs)) : Num) : Nat) := by
      simp [Computability.decodeNat,Computability.decodeNum]
    rw [he]
    change Computability.encodeNum (((Num.pos (Computability.decodePosNum (b::xs)) : Num) : Nat) : Num) = normalize (b::xs)
    rw [Num.of_to_nat]
    change Computability.encodePosNum (Computability.decodePosNum (b::xs)) = normalize (b::xs)
    rw [encode_decode_positive,normalize_eq_positive (b::xs) (by simp)]

theorem decode_eq_iff_normalize_eq (xs ys : List Bool) :
    Computability.decodeNat xs = Computability.decodeNat ys ↔ normalize xs = normalize ys := by
  constructor
  · intro h
    rw [← encode_decode_nat,← encode_decode_nat,h]
  · intro h
    rw [← encode_decode_nat,← encode_decode_nat] at h
    have hh := congrArg Computability.decodeNat h
    simpa using hh

theorem normalize_length (xs : List Bool) : (normalize xs).length ≤ xs.length+1 := by
  unfold normalize
  split <;> simp

example : normalize [false] = [false,true] := rfl
example : normalize [false,true] = [false,true] := rfl
example : Computability.decodeNat [false] = Computability.decodeNat [false,true] := by decide
example : normalize [] = [] := rfl

end Shared.ComplexityBridge.NumeralNormalization
