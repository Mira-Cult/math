import Shared.Beeping.NPcoNP.Source284Relative
import Shared.Codes.FinitePrograms

/-! A tape-level bridge from the 284 source's two numeric halves to the
shared finite-program tape. The orientation is explicit: a source turn
reverses the meaning of the two halves. This is a local step theorem, not a
finite compiler, an input initializer, or a polynomial-cost theorem. -/
namespace Shared.Beeping.NPcoNP.Source284FiniteTapeStep

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Codes.FinitePrograms

def digit (b : Bool) : Nat := if b then 1 else 0

def value : List Bool → Nat
  | [] => 0
  | b :: xs => digit b + 2 * value xs

/-- `reverse = false` means that the numeric forward half points right;
`reverse = true` means that it points left. -/
def represented (t : Tape) (reverse : Bool) (state : Nat) : Source284Relative.Config :=
  if reverse then ⟨value t.2.2, digit t.2.1 + 2 * value t.1, state⟩
  else ⟨value t.1, digit t.2.1 + 2 * value t.2.2, state⟩

/-- The numeric transition when write, turn, and destination are already
extracted from the unary instruction record. -/
def bitStep (c : Source284Relative.Config) (write turn : Bool) (next : Nat) : Source284Relative.Config :=
  if turn then ⟨2 * (c.right / 2) + digit write, c.left, next⟩
  else ⟨2 * c.left + digit write, c.right / 2, next⟩

@[simp] theorem digit_lt (b : Bool) : digit b < 2 := by cases b <;> decide

@[simp] theorem pop_head (b : Bool) (v : Nat) : (digit b + 2 * v) / 2 = v := by
  cases b <;> simp [digit] <;> omega

/-- A relative source move is exactly one shared tape move, with the new
orientation accounting for a turn. This includes infinite virtual blanks on
both ends of the finite represented tape. -/
theorem represented_step (t : Tape) (reverse write turn : Bool) (state next : Nat) :
    bitStep (represented t reverse state) write turn next =
      represented (moveTape (xor reverse turn) write t) (xor reverse turn) next := by
  rcases t with ⟨left, head, right⟩
  cases head <;> cases write <;> cases reverse <;> cases turn <;>
    cases left <;> cases right <;>
    simp [bitStep, represented, moveTape, value, digit, Bool.xor] <;> omega

/-- A unary record stores its write digit and turn digit in its two low
bits, with the destination in the remaining high bits. -/
def writeBit (r : Nat) : Bool := r % 2 == 1
def turnBit (r : Nat) : Bool := (r / 2) % 2 == 1

theorem digit_writeBit (r : Nat) : digit (writeBit r) = r % 2 := by
  have h : r % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h1 : r % 2 = 1 <;> simp [writeBit, digit, h1] <;> omega

/-- The source's numeric transition agrees with the explicit bit transition
for every active source state and every virtual-zero record. -/
theorem source_step_bits (description : Nat) (c : Source284Relative.Config)
    (hactive : c.state ≠ 0) :
    let r := record description (c.state - 1 + c.right % 2)
    Source284Relative.step description c = bitStep c (writeBit r) (turnBit r) (r / 4) := by
  dsimp only
  simp only [Source284Relative.step, hactive, ↓reduceIte, bitStep, turnBit,
    beq_iff_eq, digit_writeBit]

/-- With its current orientation as part of the finite control, one active
source step is a single physical tape transition. The record lookup is
still an explicit source operation; no finite table is claimed here. -/
theorem source_step_tape (description : Nat) (t : Tape) (reverse : Bool)
    (state : Nat) (hactive : state ≠ 0) :
    let c := represented t reverse state
    let r := record description (state - 1 + c.right % 2)
    Source284Relative.step description c =
      represented (moveTape (xor reverse (turnBit r)) (writeBit r) t)
        (xor reverse (turnBit r)) (r / 4) := by
  dsimp only
  have hs : (represented t reverse state).state ≠ 0 := by
    cases reverse <;> simpa [represented] using hactive
  have he : (represented t reverse state).state = state := by
    cases reverse <;> rfl
  rw [source_step_bits description _ hs]
  simp only [he]
  exact represented_step t reverse
    (writeBit (record description (state - 1 + (represented t reverse state).right % 2)))
    (turnBit (record description (state - 1 + (represented t reverse state).right % 2)))
    state (record description (state - 1 + (represented t reverse state).right % 2) / 4)

end Shared.Beeping.NPcoNP.Source284FiniteTapeStep
