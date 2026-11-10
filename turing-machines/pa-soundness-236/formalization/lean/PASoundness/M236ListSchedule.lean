import PASoundness.Cantor
/-! An alternative experimental self-delimiting coordinate-list stage coding; not the M236 producer schedule. -/
namespace PASoundness.M236.ListSchedule
open PASoundness.Cantor

def encode : List Nat → Nat
  | [] => 0
  | x :: xs => 1 + pair x (encode xs)

def decode (n : Nat) : List Nat :=
  if n = 0 then [] else
    (unpair (n-1)).1 :: decode (unpair (n-1)).2
termination_by n
decreasing_by
  have h := unpair_snd_le (n-1)
  omega

theorem decode_encode (xs : List Nat) : decode (encode xs) = xs := by
  induction xs with
  | nil => simp [encode, decode]
  | cons x xs ih =>
    simp [encode, decode, unpair_pair, ih]

theorem encode_decode (n : Nat) : encode (decode n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [decode]
    split
    next h => simp [h, encode]
    next h =>
      simp only [encode]
      have hl : (unpair (n-1)).2 < n := by
        have hle := unpair_snd_le (n-1)
        omega
      rw [ih _ hl, pair_unpair]
      omega

def stage (formula : Nat) (coords : List Nat) : Nat :=
  pair formula (encode coords - 1)

def atStage (n : Nat) : Nat × List Nat :=
  ((unpair n).1, decode ((unpair n).2 + 1))

/-- Every finite nonempty list is reached at its explicit stage. -/
theorem at_stage (formula : Nat) (coords : List Nat) (h : coords ≠ []) :
    atStage (stage formula coords) = (formula, coords) := by
  cases coords with
  | nil => contradiction
  | cons x xs => simp [stage, atStage, encode, decode, decode_encode, unpair_pair]

/-- Two nonempty addressed lists cannot share a stage. -/
theorem stage_injective (f g : Nat) (xs ys : List Nat)
    (hxs : xs ≠ []) (hys : ys ≠ []) (h : stage f xs = stage g ys) :
    f = g ∧ xs = ys := by
  have he := congrArg atStage h
  rw [at_stage f xs hxs, at_stage g ys hys] at he
  exact Prod.mk.inj he

/-- No natural stage is lost or duplicated by the coding. -/
theorem stage_at (n : Nat) : stage (atStage n).1 (atStage n).2 = n := by
  simp [stage, atStage, encode_decode, pair_unpair]

theorem atStage_nonempty (n : Nat) : (atStage n).2 ≠ [] := by
  intro h
  change decode ((unpair n).2 + 1) = [] at h
  have he := encode_decode ((unpair n).2 + 1)
  rw [h] at he
  simp [encode] at he

/-- Arbitrarily large coordinates and finite lengths are covered, with no
uniform bound on the stage or the list. -/
theorem coverage (formula : Nat) (x : Nat) (xs : List Nat) :
    ∃ n, atStage n = (formula, x :: xs) :=
  ⟨stage formula (x :: xs), at_stage formula (x :: xs) (by simp)⟩

end PASoundness.M236.ListSchedule
