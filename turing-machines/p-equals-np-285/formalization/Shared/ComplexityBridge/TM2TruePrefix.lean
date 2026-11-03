import Shared.ComplexityBridge.TM2ListUnaryLength

set_option backward.isDefEq.respectTransparency false

/-! Count the initial true bits of a Boolean list in unary. Every canonical
list cell costs one TM2 statement block; remaining cells are consumed after
the first false, and the machine resets its internal state on halt. -/
namespace Shared.ComplexityBridge.TM2TruePrefix
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | input | output deriving DecidableEq
inductive Label where | scan deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.scan] (by intro l; cases l; simp)
abbrev State := Bool × Option Bool

def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .scan => .pop .input (fun s h => (s.1,h))
      (.branch (fun s => s.2.isSome)
        (.pop .input (fun s h => (s.1,h))
          (.branch (fun s => s.1 && s.2.getD false)
            (.pop .input (fun _ _ => (true,none))
              (.push .output (fun _ => false) (.push .output (fun _ => true)
                (.push .output (fun _ => true) (.goto (fun _ => .scan))))))
            (.pop .input (fun _ _ => (false,none)) (.goto (fun _ => .scan)))))
        (.load (fun _ => (true,none)) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .scan
  σ := State
  initialState := (true,none)
  m := program

def stackVals (input output : List Bool) : Stack → List Bool
  | .input => input | .output => output

def cfg (active : Bool) (input output : List Bool) : machine.Cfg :=
  ⟨some .scan,(active,none),stackVals input output⟩

theorem step_cell (active b : Bool) (input output : List Bool) :
    machine.step (cfg active (true::b::false::input) output) =
      some (cfg (active && b) input (if active && b then true::true::false::output else output)) := by
  cases active <;> cases b <;>
    change some (Cfg.mk _ _ _) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

theorem step_nil (active : Bool) (output : List Bool) :
    machine.step (cfg active [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,machine]

def count : List Bool → Nat
  | [] => 0
  | b::xs => if b then count xs+1 else 0

def truePrefix (xs : List Bool) : List Bool := List.replicate (count xs) true

theorem encode_cons (b : Bool) (xs : List Bool) :
    BitstringEncoding.bitEncode (b::xs) = true::b::false::BitstringEncoding.bitEncode xs :=
  Shared.ComplexityBridge.CircuitPairWitness.encode_cons b xs

theorem scan_run (xs : List Bool) (active : Bool) (output : List Bool) :
    runSteps machine.step (xs.length+1) (cfg active (BitstringEncoding.bitEncode xs) output) =
      some (Turing.haltList machine
        (BitstringEncoding.bitEncode (if active then truePrefix xs else []) ++ output)) := by
  induction xs generalizing active output with
  | nil =>
    have he : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
    simpa [truePrefix,count,he,runSteps] using step_nil active output
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,encode_cons,runSteps_front,step_cell]
    cases active <;> cases b
    · simpa [truePrefix,count] using ih false output
    · simpa [truePrefix,count] using ih false output
    · simpa [truePrefix,count] using ih false output
    · have h := ih true (true::true::false::output)
      have hc := Shared.ComplexityBridge.TM2ListUnaryLength.encoded_tokens_commute (count xs)
      have he : BitstringEncoding.bitEncode (List.replicate (count xs) true) ++ (true::true::false::output) =
          (true::true::false::BitstringEncoding.bitEncode (List.replicate (count xs) true)) ++ output := by
        simpa [List.append_assoc] using congrArg (fun v => v++output) hc
      simpa [truePrefix,count,List.replicate_succ,encode_cons,he] using h

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg true input [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals]

theorem run (xs : List Bool) :
    runSteps machine.step (xs.length+1) (Turing.initList machine (BitstringEncoding.bitEncode xs)) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode (truePrefix xs))) := by
  rw [initial_eq]
  simpa using scan_run xs true []

noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool) truePrefix where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X+Polynomial.C 1
  outputsFun xs := by
    refine ⟨⟨xs.length+1,?_⟩,?_⟩
    · have h := run xs
      rw [runSteps_iterate] at h
      change (fun o => o.bind machine.step)^[xs.length+1]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode xs).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (truePrefix xs)).map id))
      simpa using h
    · simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
        Shared.ComplexityBridge.bitstring_list_encoded_length]
      omega

theorem prefix_isPolyTime : ComplexityTheory.IsPolyTime truePrefix := ⟨timeMachine⟩

namespace Fixtures
example : truePrefix [] = [] := rfl
example : truePrefix [true,true,false,true] = [true,true] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2TruePrefix
