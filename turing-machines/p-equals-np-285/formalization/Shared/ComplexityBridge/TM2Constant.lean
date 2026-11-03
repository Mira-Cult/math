import Shared.Codes.TM2ProgramHalt

import Shared.ComplexityBridge.TM2ListCodec

namespace Shared.ComplexityBridge.TM2Constant
open Turing.TM2 Shared.Codes.TM2Program Shared.ComplexityBridge.TM2Symbols

inductive Stack where | input | output deriving DecidableEq
inductive Label where | clear | finish deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input, .output] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.clear, .finish] (by intro l; cases l <;> simp)

def program (b : Bool) : Label → Stmt (fun _ : Stack => Bool) Label Bool
  | .clear => .pop .input (fun _ h => h.isSome)
      (.branch id (.goto (fun _ => .clear)) (.goto (fun _ => .finish)))
  | .finish => .push .output (fun _ => b) (.load (fun _ => false) .halt)

def machine (b : Bool) : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .clear
  σ := Bool
  initialState := false
  m := program b

def stackVals (input output : List Bool) : Stack → List Bool
  | .input => input | .output => output

def cfg (b : Bool) (l : Label) (v : Bool) (input output : List Bool) : (machine b).Cfg :=
  ⟨some l, v, stackVals input output⟩

theorem clear_cons (b v x : Bool) (xs output : List Bool) :
    (machine b).step (cfg b .clear v (x :: xs) output) = some (cfg b .clear true xs output) := by
  change some (Cfg.mk (some Label.clear) true (Function.update (stackVals (x :: xs) output) .input xs)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals, Function.update]

theorem clear_nil (b v : Bool) (output : List Bool) :
    (machine b).step (cfg b .clear v [] output) = some (cfg b .finish false [] output) := by
  change some (Cfg.mk (some Label.finish) false (Function.update (stackVals [] output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals, Function.update]

theorem finish_step (b : Bool) :
    (machine b).step (cfg b .finish false [] []) = some (Turing.haltList (machine b) [b]) := by
  change some (Cfg.mk (none : Option Label) false (Function.update (stackVals [] []) .output [b])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals, Function.update, Turing.haltList, machine] <;> rfl

theorem clear_run (b : Bool) (xs : List Bool) (v : Bool) :
    runSteps (machine b).step (xs.length + 1) (cfg b .clear v xs []) =
      some (cfg b .finish false [] []) := by
  induction xs generalizing v with
  | nil => exact clear_nil b v []
  | cons x xs ih =>
    rw [List.length_cons, show xs.length + 1 + 1 = (xs.length + 1) + 1 by omega,
      runSteps_front, clear_cons]
    exact ih true

theorem initial_eq (b : Bool) (input : List Bool) :
    Turing.initList (machine b) input = cfg b .clear false input [] := by
  change Cfg.mk (some Label.clear) false _ = Cfg.mk (some Label.clear) false (stackVals input [])
  congr 1; funext k; cases k <;> simp [machine, stackVals] <;> rfl

/-- The machine clears its entire input, resets its state, and halts with one bit. -/
theorem run (b : Bool) (input : List Bool) :
    runSteps (machine b).step (input.length + 2) (Turing.initList (machine b) input) =
      some (Turing.haltList (machine b) [b]) := by
  rw [show input.length + 2 = (input.length + 1) + 1 by omega, initial_eq,
    runSteps_add, clear_run]
  exact finish_step b

noncomputable def timePolynomial : Polynomial Nat := Polynomial.X + Polynomial.C 2

set_option backward.isDefEq.respectTransparency false in
noncomputable def timeMachine {α : Type} [BitstringEncoding α] (b : Bool) :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : α → List Bool)
      (BitstringEncoding.bitEncode : Bool → List Bool) (fun _ => b) where
  tm := machine b
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun a := by
    refine ⟨⟨(BitstringEncoding.bitEncode a).length + 2, ?_⟩, ?_⟩
    · have hr := run b (BitstringEncoding.bitEncode a)
      rw [runSteps_iterate] at hr
      change (fun o => o.bind (machine b).step)^[(BitstringEncoding.bitEncode a).length + 2]
        (some (Turing.initList (machine b) ((BitstringEncoding.bitEncode a).map id))) =
          some (Turing.haltList (machine b) ([b].map id))
      rw [List.map_id, List.map_id]
      exact hr
    · simp [timePolynomial]

/-- A constant Boolean relation is computable in canonical TM2 polynomial time. -/
theorem isPolyTime {α : Type} [BitstringEncoding α] (b : Bool) :
    ComplexityTheory.IsPolyTime (fun _ : α => b) := ⟨timeMachine b⟩

end Shared.ComplexityBridge.TM2Constant
