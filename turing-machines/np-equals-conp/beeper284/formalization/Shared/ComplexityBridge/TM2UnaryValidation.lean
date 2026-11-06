import Shared.ComplexityBridge.TM2ListCodec
import Shared.Codes.TM2ProgramHalt
import Shared.Codes.UnaryRequestValidation

/-! A real TM2 implementation of the unary-field validation in the executable
request parser. The raw scanner consumes its entire input even after finding a
false bit, so the halt boundary has no leftover input. -/
namespace Shared.ComplexityBridge.TM2UnaryValidation
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | input | output deriving DecidableEq
inductive Label where | scan deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input, .output] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.scan] (by intro l; cases l <;> simp)
abbrev State := Bool × Option Bool

def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .scan => .pop .input (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => (s.1 && s.2.getD false, none)) (.goto (fun _ => .scan)))
        (.push .output (fun s => s.1) (.load (fun _ => (true, none)) .halt)))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .scan
  σ := State
  initialState := (true, none)
  m := program

def stackVals (input output : List Bool) : Stack → List Bool
  | .input => input | .output => output

def cfg (acc : Bool) (input output : List Bool) : machine.Cfg :=
  ⟨some .scan, (acc, none), stackVals input output⟩

theorem step_cons (acc b : Bool) (input output : List Bool) :
    machine.step (cfg acc (b :: input) output) = some (cfg (acc && b) input output) := by
  change some (Cfg.mk (some Label.scan) (acc && b, none)
    (Function.update (stackVals (b :: input) output) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals, Function.update]

theorem step_nil (acc : Bool) :
    machine.step (cfg acc [] []) = some (Turing.haltList machine [acc]) := by
  change some (Cfg.mk (none : Option Label) ((true, none) : State)
    (Function.update (Function.update (stackVals [] []) .input []) .output [acc])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals, Function.update, machine] <;> rfl

theorem scan_run (bits : List Bool) (acc : Bool) :
    runSteps machine.step (bits.length + 1) (cfg acc bits []) =
      some (Turing.haltList machine [acc && bits.all id]) := by
  induction bits generalizing acc with
  | nil =>
    change machine.step (cfg acc [] []) = some (Turing.haltList machine [acc && true])
    simpa using step_nil acc
  | cons b bits ih =>
    rw [List.length_cons, show bits.length + 1 + 1 = (bits.length + 1) + 1 by omega,
      runSteps_front, step_cons]
    simpa [Bool.and_assoc] using ih (acc && b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg true input [] := by
  change Cfg.mk (some Label.scan) ((true, none) : State) _ =
    Cfg.mk (some Label.scan) ((true, none) : State) (stackVals input [])
  congr 1; funext k; cases k <;> simp [machine, stackVals] <;> rfl

/-- Raw bit inputs finish in exactly one block per bit plus one final block. -/
theorem run (bits : List Bool) :
    runSteps machine.step (bits.length + 1) (Turing.initList machine bits) =
      some (Turing.haltList machine [bits.all id]) := by
  rw [initial_eq]
  simpa using scan_run bits true

noncomputable def timePolynomial : Polynomial Nat := Polynomial.X + Polynomial.C 1

set_option backward.isDefEq.respectTransparency false in
noncomputable def rawTimeMachine : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (BitstringEncoding.bitEncode : Bool → List Bool)
    (fun bits : List Bool => bits.all id) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun bits := by
    refine ⟨⟨bits.length + 1, ?_⟩, ?_⟩
    · have hr := run bits
      rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[bits.length + 1]
        (some (Turing.initList machine (bits.map id))) =
          some (Turing.haltList machine ([bits.all id].map id))
      rw [List.map_id, List.map_id]
      exact hr
    · simp [timePolynomial]

/-- Unary validation includes the canonical list decoding and its time cost. -/
theorem unaryCheck_isPolyTime : ComplexityTheory.IsPolyTime
    (fun bits : List Bool => (Shared.Codes.UnaryRequestValidation.unaryCheck bits).1) := by
  obtain ⟨composed⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : Bool → List Bool) (id : List Bool → List Bool)
    (fun bits : List Bool => bits.all id)
    Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine rawTimeMachine
  have heq : (fun bits : List Bool => (Shared.Codes.UnaryRequestValidation.unaryCheck bits).1) =
      (fun bits : List Bool => bits.all id) := by
    funext bits
    exact Shared.Codes.UnaryRequestValidation.unaryCheck_correct bits
  rw [heq]
  exact ⟨composed⟩

namespace Fixtures
example : (runSteps machine.step 1 (Turing.initList machine [])).map
    (fun c => (c.l.isNone, c.stk .output)) = some (true, [true]) := by
  change (Option.map (fun c => (c.l.isNone, c.stk .output))
    (runSteps machine.step 1 (Turing.initList machine [])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 4 (Turing.initList machine [true, false, true])).map
    (fun c => (c.l.isNone, c.stk .output)) = some (true, [false]) := by
  change (Option.map (fun c => (c.l.isNone, c.stk .output))
    (runSteps machine.step 4 (Turing.initList machine [true, false, true])) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2UnaryValidation
