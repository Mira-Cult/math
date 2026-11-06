import Shared.ComplexityBridge.TM2LiteralStreamTotal

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2TagInput
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
inductive Stack where | input | scratch | output deriving DecidableEq
inductive Label where | start | scan | restore | discard deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.start,.scan,.restore,.discard] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .start => .pop .input (fun _ h => h)
      (.branch (fun v => v == some true) (.goto (fun _ => .scan)) (.goto (fun _ => .discard)))
  | .scan => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan))) (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome (.push .output (fun v => v.getD false) (.goto (fun _ => .restore))) (.load (fun _ => none) .halt))
  | .discard => .pop .input (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .discard))
        (.push .output (fun _ => true) (.load (fun _ => none) .halt)))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .start
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output
def cfg (l : Label) (flag : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,flag,stackVals input scratch output⟩

theorem start_true (input : List Bool) :
    machine.step (cfg .start none (true::input) [] []) = some (cfg .scan (some true) input [] []) := by
  change some (Cfg.mk _ _ (Function.update (stackVals (true::input) [] []) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem start_false (input : List Bool) :
    machine.step (cfg .start none (false::input) [] []) = some (cfg .discard (some false) input [] []) := by
  change some (Cfg.mk _ _ (Function.update (stackVals (false::input) [] []) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem start_nil : machine.step (cfg .start none [] [] []) = some (cfg .discard none [] [] []) := by
  change some (Cfg.mk _ _ (Function.update (stackVals [] [] []) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem discard_cons (flag : Option Bool) (b : Bool) (input : List Bool) :
    machine.step (cfg .discard flag (b::input) [] []) = some (cfg .discard (some b) input [] []) := by
  change some (Cfg.mk _ _ (Function.update (stackVals (b::input) [] []) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem discard_nil (flag : Option Bool) :
    machine.step (cfg .discard flag [] [] []) = some (Turing.haltList machine [true]) := by
  change some (Cfg.mk none (none : Option Bool) (Function.update (Function.update (stackVals [] [] []) .input []) .output [true])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine] <;> rfl

theorem discard_loop (input : List Bool) (flag : Option Bool) :
    runSteps machine.step (input.length+1) (cfg .discard flag input [] []) = some (Turing.haltList machine [true]) := by
  induction input generalizing flag with
  | nil => exact discard_nil flag
  | cons b input ih =>
    rw [List.length_cons,show input.length+1+1 = (input.length+1)+1 by omega,runSteps_front,discard_cons]
    exact ih (some b)

theorem scan_cons (flag : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .scan flag (b::input) scratch output) = some (cfg .scan (some b) input (b::scratch) output) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (stackVals (b::input) scratch output) .input input) .scratch (b::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_nil (flag : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .scan flag [] scratch output) = some (cfg .restore none [] scratch output) := by
  change some (Cfg.mk _ _ (Function.update (stackVals [] scratch output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (flag : Option Bool) (b : Bool) (scratch output : List Bool) :
    machine.step (cfg .restore flag [] (b::scratch) output) = some (cfg .restore (some b) [] scratch (b::output)) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (stackVals [] (b::scratch) output) .scratch scratch) .output (b::output))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (flag : Option Bool) (output : List Bool) :
    machine.step (cfg .restore flag [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk none (none : Option Bool) (Function.update (stackVals [] [] output) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine] <;> rfl

theorem scan_loop (input scratch output : List Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step input.length (cfg .scan flag input scratch output) =
      some (cfg .scan flag' [] (input.reverse++scratch) output) := by
  induction input generalizing scratch flag with
  | nil => exact ⟨flag,by simp [runSteps]⟩
  | cons b input ih =>
    obtain ⟨flag',h⟩ := ih (b::scratch) (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,scan_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore_loop (scratch output : List Bool) (flag : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore flag [] scratch output) =
      some (Turing.haltList machine (scratch.reverse++output)) := by
  induction scratch generalizing output flag with
  | nil =>
    change machine.step (cfg .restore flag [] [] output) = _
    simpa using restore_nil flag output
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .start none input [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals,Turing.initList] <;> rfl

/-- On a true tag keep its payload; otherwise emit an intentionally malformed
one-bit frame, which the occurrence parser rejects. -/
def selectStream (input : List Bool) : List Bool :=
  match input with | true::tail => tail | _ => [true]

theorem run (input : List Bool) :
    ∃ t ≤ 2*input.length+3, runSteps machine.step t (Turing.initList machine input) =
      some (Turing.haltList machine (selectStream input)) := by
  cases input with
  | nil =>
    refine ⟨2,by simp,?_⟩
    rw [initial_eq,show 2=1+1 by decide,runSteps_front,start_nil]
    exact discard_nil none
  | cons b input => cases b with
    | false =>
      refine ⟨input.length+2,by simp; omega,?_⟩
      have hr := discard_loop input (some false)
      rw [initial_eq,show input.length+2 = (input.length+1)+1 by omega,runSteps_front,start_false]
      exact hr
    | true =>
      obtain ⟨v,hs⟩ := scan_loop input [] [] (some true)
      simp only [List.append_nil] at hs
      have hr := restore_loop input.reverse [] none
      simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
      refine ⟨2*input.length+3,by simp,?_⟩
      have hn : 2*input.length+3 = 1+(input.length+(1+(input.length+1))) := by omega
      rw [initial_eq,hn,runSteps_add]
      change (machine.step (cfg .start none (true::input) [] [])).bind _ = _
      rw [start_true]
      change runSteps machine.step (input.length+(1+(input.length+1))) (cfg .scan (some true) input [] []) = _
      rw [runSteps_add,hs]
      change runSteps machine.step (1+(input.length+1)) (cfg .scan v [] input.reverse []) = _
      rw [runSteps_add]
      change (machine.step (cfg .scan v [] input.reverse [])).bind _ = _
      rw [scan_nil]
      exact hr

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2*Polynomial.X+Polynomial.C 3
noncomputable def rawTimeMachine : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (id : List Bool → List Bool) selectStream where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun input := by
    let t := Classical.choose (run input)
    have ht := (Classical.choose_spec (run input)).1
    have hr := (Classical.choose_spec (run input)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t] (some (Turing.initList machine (input.map id))) =
        some (Turing.haltList machine ((selectStream input).map id))
      rw [List.map_id,List.map_id]
      simpa [t] using hr
    · change t ≤ timePolynomial.eval input.length
      simpa [timePolynomial] using ht

theorem selectStream_isPolyTime : ComplexityTheory.IsPolyTime selectStream := by
  obtain ⟨first⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool) (id : List Bool → List Bool)
    (id : List Bool → List Bool) selectStream Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine rawTimeMachine
  obtain ⟨second⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool) selectStream (id : List Bool → List Bool)
    first Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine
  exact ⟨second⟩

namespace Fixtures
example : (runSteps machine.step 2 (Turing.initList machine [])).map (fun q => (q.l.isNone,q.stk .output)) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .output)) (runSteps machine.step 2 (Turing.initList machine [])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 7 (Turing.initList machine [true,false,true])).map (fun q => (q.l.isNone,q.stk .output)) = some (true,[false,true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .output)) (runSteps machine.step 7 (Turing.initList machine [true,false,true])) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2TagInput
