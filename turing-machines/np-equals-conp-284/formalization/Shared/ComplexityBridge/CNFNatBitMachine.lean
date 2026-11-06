import Shared.ComplexityBridge.CNFNatBitCosts
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false

/-! A literal finite TM2 that reverses an already-binary natural-number
encoding onto its output stack. Each source bit costs one statement block;
constructing the binary representation remains a separate input obligation. -/
namespace Shared.ComplexityBridge.CNFNatBitMachine
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | input | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.output] (by intro s; cases s <;> simp)

def program : Unit → Stmt (fun _ : Stack => Bool) Unit (Option Bool)
  | () => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun v => v.getD false) (.goto (fun _ => ())))
        (.load (fun _ => none) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input output : List Bool) : Stack → List Bool
  | .input => input | .output => output

def cfg (v : Option Bool) (input output : List Bool) : machine.Cfg :=
  ⟨some (),v,stackVals input output⟩

theorem step_cons (v : Option Bool) (b : Bool) (input output : List Bool) :
    machine.step (cfg v (b::input) output) = some (cfg (some b) input (b::output)) := by
  change some (Cfg.mk (some ()) (some b)
    (Function.update (Function.update (stackVals (b::input) output) .input input) .output (b::output))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem step_empty (v : Option Bool) (output : List Bool) :
    machine.step (cfg v [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk (none : Option Unit) (none : Option Bool) (Function.update (stackVals [] output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,machine]

theorem run_copy (bits output : List Bool) (v : Option Bool) :
    runSteps machine.step (bits.length+1) (cfg v bits output) =
      some (Turing.haltList machine (bits.reverse++output)) := by
  induction bits generalizing output v with
  | nil => exact step_empty v output
  | cons b bits ih =>
    rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,
      runSteps_front,step_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem initial_eq (bits : List Bool) : Turing.initList machine bits = cfg none bits [] := by
  change Cfg.mk (some ()) none _ = Cfg.mk (some ()) none (stackVals bits [])
  congr 1; funext k; cases k <;> simp [machine,stackVals]

/-- The machine consumes an explicitly supplied binary numeral and outputs
the reversed pinned natural-number encoding in `bitlength+1` TM2 blocks. -/
theorem encodeNat_reverse (n : Nat) :
    runSteps machine.step (n.bits.length+1) (Turing.initList machine n.bits) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode n).reverse) := by
  have h := run_copy n.bits [] none
  rw [← initial_eq] at h
  have he : BitstringEncoding.bitEncode n = n.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
  simpa [he] using h

namespace Fixtures
example : runSteps machine.step 1 (Turing.initList machine []) = some (Turing.haltList machine []) := by
  rw [initial_eq]
  simpa using run_copy [] [] none
example : runSteps machine.step 4 (Turing.initList machine [true,false,true]) =
    some (Turing.haltList machine [true,false,true]) := by
  rw [initial_eq]
  simpa using run_copy [true,false,true] [] none
end Fixtures
end Shared.ComplexityBridge.CNFNatBitMachine
