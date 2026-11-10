import PASoundness.LocalSimulation

/-!
Executable natural-register primitives used by the pinned direct compiler:
increment, decrement/test, and the two bit emissions. Finite control selects
the next instruction from the primitive's success result. This interface does
not assert correctness of the Python grammar compiler or the unary tape bank.
-/
namespace PASoundness.RegisterMachine

abbrev Bank (registers : Nat) := Fin registers → Nat

def write {registers : Nat} (bank : Bank registers) (r : Fin registers) (value : Nat) :
    Bank registers := fun q => if q = r then value else bank q

@[simp] theorem write_read {registers : Nat} (bank : Bank registers)
    (r : Fin registers) (value : Nat) : write bank r value r = value := by
  simp [write]

theorem write_other {registers : Nat} (bank : Bank registers)
    (r q : Fin registers) (value : Nat) (h : q ≠ r) :
    write bank r value q = bank q := by simp [write, h]

inductive Primitive (registers : Nat) where
  | inc : Fin registers → Primitive registers
  | decNZ : Fin registers → Primitive registers
  | emit : Bool → Primitive registers
  deriving DecidableEq, Repr

structure Outcome (registers : Nat) where
  bank : Bank registers
  success : Bool
  output : List Bool

/-- Increment succeeds; decrement succeeds exactly on a positive counter and
then removes one. Emission succeeds and leaves all registers unchanged. -/
def execute {registers : Nat} : Primitive registers → Bank registers → Outcome registers
  | .inc r, bank => ⟨write bank r (bank r + 1), true, []⟩
  | .decNZ r, bank => match bank r with
    | 0 => ⟨bank, false, []⟩
    | value+1 => ⟨write bank r value, true, []⟩
  | .emit b, bank => ⟨bank, true, [b]⟩

theorem inc_correct {registers : Nat} (bank : Bank registers) (r : Fin registers) :
    (execute (.inc r) bank).bank r = bank r + 1 ∧
      (execute (.inc r) bank).success = true ∧
        (execute (.inc r) bank).output = [] := by
  simp [execute]

theorem decNZ_zero {registers : Nat} (bank : Bank registers) (r : Fin registers)
    (h : bank r = 0) : execute (.decNZ r) bank = ⟨bank, false, []⟩ := by
  simp [execute, h]

theorem decNZ_succ {registers : Nat} (bank : Bank registers) (r : Fin registers)
    (value : Nat) (h : bank r = value+1) :
    execute (.decNZ r) bank = ⟨write bank r value, true, []⟩ := by
  simp [execute, h]

theorem decNZ_success_iff {registers : Nat} (bank : Bank registers) (r : Fin registers) :
    (execute (.decNZ r) bank).success = true ↔ 0 < bank r := by
  cases h : bank r <;> simp [execute, h]

theorem inc_preserves_other {registers : Nat} (bank : Bank registers)
    (r q : Fin registers) (h : q ≠ r) : (execute (.inc r) bank).bank q = bank q :=
  write_other bank r q _ h

theorem decNZ_preserves_other {registers : Nat} (bank : Bank registers)
    (r q : Fin registers) (h : q ≠ r) : (execute (.decNZ r) bank).bank q = bank q := by
  cases hr : bank r <;> simp [execute, hr, write, h]

theorem emit_correct {registers : Nat} (bank : Bank registers) (b : Bool) :
    execute (.emit b) bank = ⟨bank, true, [b]⟩ := rfl

theorem output_singleton {registers : Nat} (op : Primitive registers) (bank : Bank registers) :
    (execute op bank).output.length ≤ 1 := by
  cases op with
  | inc => simp [execute]
  | emit => simp [execute]
  | decNZ r => cases h : bank r <;> simp [execute, h]

structure Instruction (registers states : Nat) where
  operation : Primitive registers
  yes : Fin states
  no : Fin states

structure Config (registers states : Nat) where
  state : Fin states
  bank : Bank registers

structure Program (registers states : Nat) where
  code : Vector (Instruction registers states) states
  start : Fin states

def Program.system {registers states : Nat} (program : Program registers states) :
    WordEventSystem (Config registers states) Bool where
  initial := ⟨program.start, fun _ => 0⟩
  step := fun c =>
    let instruction := program.code[c.state]
    let result := execute instruction.operation c.bank
    (⟨if result.success then instruction.yes else instruction.no, result.bank⟩, result.output)

theorem program_physicalBits {registers states : Nat} (program : Program registers states) :
    program.system.PhysicalBits := by
  intro time
  exact output_singleton _ _

end PASoundness.RegisterMachine
