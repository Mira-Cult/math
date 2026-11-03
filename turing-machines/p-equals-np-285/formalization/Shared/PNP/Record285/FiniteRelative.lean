import Shared.PNP.Record285.RelativeTape

/-! Compile each fixed numeric relative program to finite absolute-direction
binary rows. This gives an exact semantic finite-control interface; it does not
prove a polynomial-time table builder or a canonical complexity-class bound. -/
namespace Shared.PNP.Record285.FiniteRelative
open Shared.PNP.Record285.RelativeTape

def stateCap (bits : Nat) : Nat := max 1 (bits/4) + 1

structure FiniteRow (bits : Nat) where
  write : Bool
  moveLeft : Bool
  next : Option (Fin (stateCap bits))

/-- A finite row is a function only of finite control, facing and read symbol.
It folds the relative turn bit into the ordinary absolute move direction. -/
def finiteRow (program bits : Nat) (hprogram : program < 2^bits)
    (state : Fin (stateCap bits)) (facingLeft read : Bool) : FiniteRow bits :=
  let a := rowAction program state.val read false
  let target : Fin (stateCap bits) := ⟨a.next, by
    have h : a.next ≤ bits/4 := rowAction_next_le_bits program state.val bits read false hprogram
    exact Nat.lt_succ_of_le (Nat.le_trans h (Nat.le_max_right _ _))⟩
  ⟨a.write, facingLeft != a.turn, if a.next = 0 then none else some target⟩

structure FiniteConfig (bits : Nat) where
  state : Fin (stateCap bits)
  tape : TapeConfig

def absoluteStep (c : TapeConfig) (write moveLeft : Bool) : TapeConfig :=
  ⟨writeTape c write, c.head + (if moveLeft then -1 else 1), moveLeft⟩

@[simp] theorem relative_absolute_step (c : TapeConfig) (write turn : Bool) :
    physicalStep c write turn = absoluteStep c write (c.facingLeft != turn) := rfl

def finiteStep (program bits : Nat) (hprogram : program < 2^bits)
    (c : FiniteConfig bits) : Option (FiniteConfig bits) :=
  let row := finiteRow program bits hprogram c.state c.tape.facingLeft (c.tape.tape c.tape.head)
  row.next.map fun target => ⟨target, absoluteStep c.tape row.write row.moveLeft⟩

def embed (c : FiniteConfig bits) : RelativeConfig := ⟨c.state.val, c.tape, 0⟩

/-- The entire ordinary tape, head and facing are identical after every live
step; HALT coincides exactly. -/
theorem finiteStep_matches (program bits : Nat) (hprogram : program < 2^bits)
    (c : FiniteConfig bits) :
    (finiteStep program bits hprogram c).map embed = relativeStep program (embed c) := by
  unfold finiteStep finiteRow relativeStep embed
  dsimp only
  split <;> simp_all [absoluteStep, physicalStep]

def finiteRun (program bits : Nat) (hprogram : program < 2^bits) :
    Nat → FiniteConfig bits → Option (FiniteConfig bits)
  | 0, c => some c
  | clock+1, c =>
    match finiteStep program bits hprogram c with
    | none => none
    | some next => finiteRun program bits hprogram clock next

theorem finiteRun_matches (program bits : Nat) (hprogram : program < 2^bits)
    (clock : Nat) (c : FiniteConfig bits) :
    (finiteRun program bits hprogram clock c).map embed = relativeRun program clock (embed c) := by
  induction clock generalizing c with
  | zero => rfl
  | succ clock ih =>
    have hs := finiteStep_matches program bits hprogram c
    cases hf : finiteStep program bits hprogram c with
    | none =>
      simp only [hf, Option.map_none] at hs
      simp [finiteRun, hf, relativeRun, ← hs]
    | some next =>
      simp only [hf, Option.map_some] at hs
      simpa [finiteRun, hf, relativeRun, ← hs] using ih next


/-- The initial absolute-direction control is state one facing right. -/
def finiteInitial (bits input : Nat) : FiniteConfig bits :=
  ⟨⟨1, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩, ⟨inputTape input, 0, false⟩⟩

@[simp] theorem embed_finiteInitial (bits input : Nat) :
    embed (finiteInitial bits input) = initialRelative input 0 := rfl

/-- Every fixed numeric candidate is represented by finite absolute-direction
binary rows with the same bounded HALT behavior on every canonical input. -/
theorem candidate_finiteRun_iff (program bits : Nat) (hprogram : program < 2^bits)
    (exponent n radix remaining : Nat) :
    Source.candidate program exponent n radix remaining = true ↔
      finiteRun program bits hprogram ((n+2)^exponent)
        (finiteInitial bits (Source.frame radix remaining)) = none := by
  rw [candidate_halts_iff]
  have h := finiteRun_matches program bits hprogram ((n+2)^exponent)
    (finiteInitial bits (Source.frame radix remaining))
  rw [embed_finiteInitial] at h
  rw [← h]
  cases finiteRun program bits hprogram ((n+2)^exponent)
    (finiteInitial bits (Source.frame radix remaining)) <;> simp

end Shared.PNP.Record285.FiniteRelative
