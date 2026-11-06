import Shared.ComplexityBridge.NumeralNormalization
import Shared.ComplexityBridge.TM2ListCodec

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2NumeralNormalize
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
inductive Stack where | input | scratch | output
  deriving DecidableEq
inductive Label where | scan | restore
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.scan,.restore] (by intro l; cases l <;> simp)
abbrev State := Option Bool × Option Bool

def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .scan => .pop .input (fun s h => (h,s.2))
      (.branch (fun s => s.1.isSome)
        (.push .scratch (fun s => s.1.getD false)
          (.load (fun s => (none,s.1)) (.goto (fun _ => .scan))))
        (.branch (fun s => s.2 == some false)
          (.push .output (fun _ => true) (.load (fun _ => (none,none)) (.goto (fun _ => .restore))))
          (.load (fun _ => (none,none)) (.goto (fun _ => .restore)))))
  | .restore => .pop .scratch (fun s h => (h,s.2))
      (.branch (fun s => s.1.isSome) (.push .output (fun s => s.1.getD false) (.goto (fun _ => .restore)))
        (.load (fun _ => (none,none)) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .scan
  σ := State
  initialState := (none,none)
  m := program

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

def cfg (l : Label) (v last : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,(v,last),stackVals input scratch output⟩

theorem scan_cons (v last : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .scan v last (b::input) scratch output) = some (cfg .scan none (some b) input (b::scratch) output) := by
  change some (Cfg.mk (some Label.scan) (none,some b)
    (Function.update (Function.update (stackVals (b::input) scratch output) .input input) .scratch (b::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_nil (v last : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .scan v last [] scratch output) =
      some (cfg .restore none none [] scratch (if last = some false then true::output else output)) := by
  cases last with
  | none =>
    change some (Cfg.mk (some Label.restore) (none,none) (Function.update (stackVals [] scratch output) .input [])) = _
    congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]
  | some b => cases b with
    | false =>
      change some (Cfg.mk (some Label.restore) (none,none)
        (Function.update (Function.update (stackVals [] scratch output) .input []) .output (true::output))) = _
      congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]
    | true =>
      change some (Cfg.mk (some Label.restore) (none,none) (Function.update (stackVals [] scratch output) .input [])) = _
      congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v last : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .restore v last input (b::scratch) output) = some (cfg .restore (some b) last input scratch (b::output)) := by
  change some (Cfg.mk (some Label.restore) (some b,last)
    (Function.update (Function.update (stackVals input (b::scratch) output) .scratch scratch) .output (b::output))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v last : Option Bool) (output : List Bool) :
    machine.step (cfg .restore v last [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk (none : Option Label) ((none,none) : State) (Function.update (stackVals [] [] output) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine] <;> rfl

theorem scan_run (bits scratch output : List Bool) (last : Option Bool) :
    runSteps machine.step bits.length (cfg .scan none last bits scratch output) =
      some (cfg .scan none (Shared.ComplexityBridge.NumeralNormalization.lastSeen bits last) [] (bits.reverse++scratch) output) := by
  induction bits generalizing scratch last with
  | nil => rfl
  | cons b bits ih =>
    rw [List.length_cons,runSteps_front,scan_cons]
    simpa [Shared.ComplexityBridge.NumeralNormalization.lastSeen,List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restore_run (scratch output : List Bool) (v last : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v last [] scratch output) =
      some (Turing.haltList machine (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact restore_nil v last output
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .scan none none input [] [] := by
  change Cfg.mk (some Label.scan) (none,none) _ = Cfg.mk (some Label.scan) (none,none) (stackVals input [] [])
  congr 1; funext k; cases k <;> simp [machine,stackVals] <;> rfl

/-- Starting from raw input, compute the pinned numeral normalization and
clear every other stack. The cost is exactly `2*input.length+2` TM2 blocks. -/
theorem run (bits : List Bool) :
    runSteps machine.step (2*bits.length+2) (Turing.initList machine bits) =
      some (Turing.haltList machine (Shared.ComplexityBridge.NumeralNormalization.normalize bits)) := by
  have hs := scan_run bits [] [] none
  simp only [List.append_nil] at hs
  let suffix := if Shared.ComplexityBridge.NumeralNormalization.lastSeen bits none = some false then [true] else []
  have hr := restore_run bits.reverse suffix none none
  simp only [List.reverse_reverse,List.length_reverse] at hr
  have hn : 2*bits.length+2 = bits.length+((bits.length+1)+1) := by omega
  rw [hn,initial_eq,runSteps_add,hs]
  change runSteps machine.step ((bits.length+1)+1)
    (cfg .scan none (Shared.ComplexityBridge.NumeralNormalization.lastSeen bits none) [] bits.reverse []) = _
  rw [runSteps_front,scan_nil]
  change runSteps machine.step (bits.length+1) (cfg .restore none none [] bits.reverse suffix) = _
  simpa [Shared.ComplexityBridge.NumeralNormalization.normalize,suffix] using hr

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2*Polynomial.X + Polynomial.C 2

set_option backward.isDefEq.respectTransparency false in
noncomputable def rawTimeMachine : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (id : List Bool → List Bool)
    Shared.ComplexityBridge.NumeralNormalization.normalize where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun bits := by
    refine ⟨⟨2*bits.length+2,?_⟩,?_⟩
    · have hr := run bits
      rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[2*bits.length+2]
        (some (Turing.initList machine (bits.map id))) =
          some (Turing.haltList machine ((Shared.ComplexityBridge.NumeralNormalization.normalize bits).map id))
      rw [List.map_id,List.map_id]
      exact hr
    · simp [timePolynomial]

/-- The canonical complexity class includes normalization, with the raw/list
boundary codecs and both composition costs charged. -/
theorem normalize_isPolyTime : ComplexityTheory.IsPolyTime Shared.ComplexityBridge.NumeralNormalization.normalize := by
  obtain ⟨first⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool) (id : List Bool → List Bool)
    (id : List Bool → List Bool) Shared.ComplexityBridge.NumeralNormalization.normalize
    Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine rawTimeMachine
  obtain ⟨second⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    Shared.ComplexityBridge.NumeralNormalization.normalize (id : List Bool → List Bool)
    first Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine
  exact ⟨second⟩

namespace Fixtures
example : (runSteps machine.step 4 (Turing.initList machine [false])).map
    (fun c => (c.l.isNone,c.stk .output)) = some (true,[false,true]) := by
  change (Option.map (fun c => (c.l.isNone,c.stk .output))
    (runSteps machine.step 4 (Turing.initList machine [false])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 2 (Turing.initList machine [])).map
    (fun c => (c.l.isNone,c.stk .output)) = some (true,([] : List Bool)) := by
  change (Option.map (fun c => (c.l.isNone,c.stk .output))
    (runSteps machine.step 2 (Turing.initList machine [])) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2NumeralNormalize
