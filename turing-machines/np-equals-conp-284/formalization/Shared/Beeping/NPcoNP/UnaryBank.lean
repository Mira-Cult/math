import Mathlib.Tactic

/-! Finite words for the unary register bank described in the native-HALF
proof at Mira-Cult/math-wip commit `7b90875183aa928fb19a4a9bf333b8ced2194ded`,
`problems/np-conp-formulations/selector/continuation/compact/compiler/native/PROOF.md`.
Each natural value x is represented by `1^(x+1)0`.  The designated dummy
block is nonempty; a finite zero-valued reserve may follow the active bank.
This module specifies finite words only: it does not assert that any binary
table realizes a scan, shift, boot, head position, or event behavior. -/

namespace Shared.Beeping.NPcoNP.UnaryBank

/-- The trailing zero is the separator after the nonempty unary block. -/
def block (n : Nat) : List Bool := List.replicate (n + 1) true ++ [false]

def encode : List Nat → List Bool
  | [] => []
  | n :: ns => block n ++ encode ns

/-- A finite prepared word: control pre, zero separator, dummy block,
active bank, zero reserve and a further zero giving a double-zero end.
The meaning and head alignment of `pre` are not fixed here. -/
def prepared (pre : List Bool) (dummy : Nat) (values : List Nat)
    (reserve : Nat) : List Bool :=
  pre ++ [false] ++ block dummy ++ encode values ++
    encode (List.replicate reserve 0) ++ [false]

@[simp] theorem block_zero : block 0 = [true, false] := by rfl

theorem block_nonempty (n : Nat) : block n ≠ [] := by
  simp [block]

@[simp] theorem block_length (n : Nat) : (block n).length = n + 2 := by
  simp [block]

theorem encode_append (xs ys : List Nat) : encode (xs ++ ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, ih, List.append_assoc]

@[simp] theorem encode_single (n : Nat) : encode [n] = block n := by simp [encode]

theorem reserve_succ (n : Nat) :
    encode (List.replicate (n + 1) 0) = encode (List.replicate n 0) ++ [true, false] := by
  rw [List.replicate_succ', encode_append]
  rfl

/-- Inserting one additional zero-valued bank cell appends exactly `10`
after the active bank. This is a representation identity, not a machine run. -/
theorem append_zero_block (xs : List Nat) : encode (xs ++ [0]) = encode xs ++ [true, false] := by
  rw [encode_append]
  rfl

/-- The full finite windows for a gap-closing suffix shift. The two initial
zeros are the designated gap; the two final zeros supply the scanned blank
tail. The output shifts the suffix one cell left and appends one zero cell.
These words are defined even for an empty suffix; the producer's four-state
physical scan and its empty-suffix behavior are not justified by this list
identity. -/
def shiftBefore (pre : List Bool) (suffix : List Nat) : List Bool :=
  pre ++ [false, false] ++ encode suffix ++ [false, false]

def shiftAfter (pre : List Bool) (suffix : List Nat) : List Bool :=
  pre ++ [false] ++ encode suffix ++ [true, false, false]

theorem shiftAfter_as_extended_bank (pre : List Bool) (suffix : List Nat) :
    shiftAfter pre suffix = pre ++ [false] ++ encode (suffix ++ [0]) ++ [false] := by
  simp [shiftAfter, append_zero_block, List.append_assoc]

theorem shift_window_length (pre : List Bool) (suffix : List Nat) :
    (shiftBefore pre suffix).length = (shiftAfter pre suffix).length := by
  simp [shiftBefore, shiftAfter]

theorem shift_pre_preserved (pre : List Bool) (suffix : List Nat) :
    pre <+: shiftAfter pre suffix := by
  exact ⟨[false] ++ encode suffix ++ [true, false, false], by simp [shiftAfter, List.append_assoc]⟩

theorem shift_before_suffix (pre : List Bool) (suffix : List Nat) :
    (shiftBefore pre suffix).drop (pre.length + 2) = encode suffix ++ [false, false] := by
  simp [shiftBefore, List.drop_append]

theorem shift_after_suffix (pre : List Bool) (suffix : List Nat) :
    (shiftAfter pre suffix).drop (pre.length + 1) = encode suffix ++ [true, false, false] := by
  simp [shiftAfter, List.drop_append]

theorem shift_before_frame (pre : List Bool) (suffix : List Nat) :
    (shiftBefore pre suffix).take pre.length = pre := by
  simp [shiftBefore]

theorem shift_after_frame (pre : List Bool) (suffix : List Nat) :
    (shiftAfter pre suffix).take pre.length = pre := by
  simp [shiftAfter]

/-- Scan a finite run of ones up to the first zero. A missing delimiter is
reported as failure. The count includes any supplied accumulator. -/
def scan (k : Nat) : List Bool → Option (Nat × List Bool)
  | [] => none
  | true :: xs => scan (k + 1) xs
  | false :: xs => some (k, xs)

theorem scan_replicate (n k : Nat) (xs : List Bool) :
    scan k (List.replicate n true ++ false :: xs) = some (k+n, xs) := by
  induction n generalizing k with
  | zero => simp [scan]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, scan]
    rw [ih]
    simp [Nat.add_comm, Nat.add_left_comm]

/-- Require one or more ones, then decode the value excluding the base one. -/
def readBlock (xs : List Bool) : Option (Nat × List Bool) := do
  let (count, rest) ← scan 0 xs
  match count with
  | 0 => none
  | n+1 => some (n, rest)

theorem readBlock_encode (n : Nat) (tail : List Bool) :
    readBlock (block n ++ tail) = some (n, tail) := by
  simp only [readBlock, block, List.append_assoc, List.cons_append, List.nil_append]
  rw [scan_replicate]
  simp

/-- Read exactly the requested number of blocks, preserving the tail. -/
def decode : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bits => some ([], bits)
  | fuel+1, bits => do
    let (n, rest) ← readBlock bits
    let (ns, rest') ← decode fuel rest
    pure (n::ns, rest')

theorem decode_encode (values : List Nat) (tail : List Bool) :
    decode values.length (encode values ++ tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons n ns ih =>
    simp [decode, encode, List.append_assoc, readBlock_encode, ih]

@[simp] theorem falseCount_encode (xs : List Nat) :
    (encode xs).count false = xs.length := by
  induction xs with
  | nil => rfl
  | cons n ns ih => simp [encode, block, ih, List.count_replicate]

theorem encode_injective : Function.Injective encode := by
  intro xs ys h
  have hl : xs.length = ys.length := by
    simpa using congrArg (List.count false) h
  have hx := decode_encode xs []
  have hy := decode_encode ys []
  simp only [List.append_nil] at hx hy
  rw [h, hl, hy] at hx
  have hp := Option.some.inj hx
  have hf := congrArg Prod.fst hp
  exact hf.symm

/-- The old active suffix remains recoverable from the before window. -/
theorem decode_shift_before (pre : List Bool) (suffix : List Nat) :
    decode suffix.length ((shiftBefore pre suffix).drop (pre.length + 2)) =
      some (suffix, [false, false]) := by
  rw [shift_before_suffix]
  exact decode_encode suffix [false, false]

/-- After the specified rewrite, the decoder recovers every old suffix
value and one additional zero-valued reserve block. -/
theorem decode_shift_after (pre : List Bool) (suffix : List Nat) :
    decode (suffix.length + 1) ((shiftAfter pre suffix).drop (pre.length + 1)) =
      some (suffix ++ [0], [false]) := by
  rw [shift_after_suffix]
  have h := decode_encode (suffix ++ [0]) [false]
  simpa [append_zero_block, List.append_assoc] using h

example (rest : List Bool) : readBlock (false :: rest) = none := rfl

end Shared.Beeping.NPcoNP.UnaryBank
