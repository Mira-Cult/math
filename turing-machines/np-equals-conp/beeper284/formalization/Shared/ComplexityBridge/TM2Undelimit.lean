import Shared.ComplexityBridge.CNFWitness

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2Undelimit
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | input | scratch | payload
  deriving DecidableEq
inductive Label where | header | data | restore | done | reject
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.payload] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.header,.data,.restore,.done,.reject] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .header => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true) (.goto (fun _ => .data)) (.goto (fun _ => .restore)))
        (.goto (fun _ => .reject)))
  | .data => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .header)))
        (.goto (fun _ => .reject)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome (.push .payload (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)
  | .reject => .goto (fun _ => .reject)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .payload
  Γ := fun _ => Bool
  Λ := Label
  main := .header
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch payload : List Bool) : Stack → List Bool
  | .input => input
  | .scratch => scratch
  | .payload => payload

def cfg (l : Label) (v : Option Bool) (input scratch payload : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch payload⟩

theorem header_true (v : Option Bool) (input scratch payload : List Bool) :
    machine.step (cfg .header v (true::input) scratch payload) = some (cfg .data (some true) input scratch payload) := by
  change some (Cfg.mk (some Label.data) (some true)
    (Function.update (stackVals (true::input) scratch payload) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_false (v : Option Bool) (input scratch payload : List Bool) :
    machine.step (cfg .header v (false::input) scratch payload) = some (cfg .restore (some false) input scratch payload) := by
  change some (Cfg.mk (some Label.restore) (some false)
    (Function.update (stackVals (false::input) scratch payload) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_nil (v : Option Bool) (scratch payload : List Bool) :
    machine.step (cfg .header v [] scratch payload) = some (cfg .reject none [] scratch payload) := by
  change some (Cfg.mk (some Label.reject) none (Function.update (stackVals [] scratch payload) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem data_cons (v : Option Bool) (b : Bool) (input scratch payload : List Bool) :
    machine.step (cfg .data v (b::input) scratch payload) = some (cfg .header (some b) input (b::scratch) payload) := by
  change some (Cfg.mk (some Label.header) (some b)
    (Function.update (Function.update (stackVals (b::input) scratch payload) .input input) .scratch (b::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem data_nil (v : Option Bool) (scratch payload : List Bool) :
    machine.step (cfg .data v [] scratch payload) = some (cfg .reject none [] scratch payload) := by
  change some (Cfg.mk (some Label.reject) none (Function.update (stackVals [] scratch payload) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (input scratch payload : List Bool) :
    machine.step (cfg .restore v input (b::scratch) payload) = some (cfg .restore (some b) input scratch (b::payload)) := by
  change some (Cfg.mk (some Label.restore) (some b)
    (Function.update (Function.update (stackVals input (b::scratch) payload) .scratch scratch) .payload (b::payload))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (input payload : List Bool) :
    machine.step (cfg .restore v input [] payload) = some (cfg .done none input [] payload) := by
  change some (Cfg.mk (some Label.done) none (Function.update (stackVals input [] payload) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

/-- Each payload symbol costs two blocks and is reversed on scratch. -/
theorem header_run (bits tail scratch payload : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (2*bits.length) (cfg .header v (BitstringEncoding.delimit bits ++ tail) scratch payload) =
      some (cfg .header v' (false::tail) (bits.reverse++scratch) payload) := by
  induction bits generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit]⟩
  | cons b bits ih =>
    obtain ⟨v',h⟩ := ih (b::scratch) (some b)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(bits.length+1) = (2*bits.length+1)+1 := by omega
    rw [hn,runSteps_front,header_true]
    change runSteps machine.step (2*bits.length+1)
      (cfg .data (some true) (b::(BitstringEncoding.delimit bits ++ tail)) scratch payload) = _
    rw [runSteps_front,data_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore_run (scratch input payload : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore v input scratch payload) =
      some (cfg .restore v' input [] (scratch.reverse++payload)) := by
  induction scratch generalizing payload v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b scratch ih =>
    obtain ⟨v',h⟩ := ih (b::payload) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .header none input [] [] := by
  change Cfg.mk (some Label.header) none _ = Cfg.mk (some Label.header) none (stackVals input [] [])
  congr 1
  funext k
  cases k <;> simp [machine,stackVals] <;> rfl

/-- A well-formed block is decoded and its suffix preserved in exactly
`3*payload.length+2` TM2 statement blocks. -/
theorem valid_run (bits tail : List Bool) :
    runSteps machine.step (3*bits.length+2) (Turing.initList machine (BitstringEncoding.delimit bits ++ tail)) =
      some (cfg .done none tail [] bits) := by
  obtain ⟨v,hh⟩ := header_run bits tail [] [] none
  simp only [List.append_nil] at hh
  obtain ⟨u,hr⟩ := restore_run bits.reverse tail [] (some false)
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hr
  have hrc : runSteps machine.step (bits.length+1) (cfg .restore (some false) tail bits.reverse []) =
      some (cfg .done none tail [] bits) := by
    rw [runSteps_add,hr]
    exact restore_nil u tail bits
  have hn : 3*bits.length+2 = 2*bits.length+((bits.length+1)+1) := by omega
  rw [hn,initial_eq,runSteps_add,hh]
  change runSteps machine.step ((bits.length+1)+1) (cfg .header v (false::tail) bits.reverse []) = _
  rw [runSteps_front,header_false]
  exact hrc

/-- An invalid block consumes its finite input and reaches the reject label;
partial payload is never reported as a successful parse. -/
theorem invalid_run (input scratch payload : List Bool) (v : Option Bool)
    (h : BitstringEncoding.undelimit input = none) :
    ∃ t ≤ input.length+1, ∃ scratch',
      runSteps machine.step t (cfg .header v input scratch payload) = some (cfg .reject none [] scratch' payload) := by
  induction input using List.twoStepInduction generalizing scratch v with
  | nil => exact ⟨1,by simp,scratch,header_nil v scratch payload⟩
  | singleton b =>
    cases b with
    | false => simp [BitstringEncoding.undelimit] at h
    | true =>
      refine ⟨2,by simp,scratch,?_⟩
      rw [show 2 = 1+1 by decide,runSteps_front,header_true]
      exact data_nil (some true) scratch payload
  | cons_cons b c input ih =>
    cases b with
    | false => simp [BitstringEncoding.undelimit] at h
    | true =>
      have htail : BitstringEncoding.undelimit input = none := by
        cases hu : BitstringEncoding.undelimit input <;> simp [BitstringEncoding.undelimit,hu] at h ⊢
      obtain ⟨t,ht,scratch',hr⟩ := ih (c::scratch) (some c) htail
      refine ⟨t+2,by simp only [List.length_cons]; omega,scratch',?_⟩
      rw [show t+2 = (t+1)+1 by omega,runSteps_front,header_true]
      change runSteps machine.step (t+1) (cfg .data (some true) (c::input) scratch payload) = _
      rw [runSteps_front,data_cons]
      exact hr

/-- On all raw inputs, the finite parser terminates at the correct branch. -/
theorem parse_progress (input : List Bool) :
    (∃ payload tail, BitstringEncoding.undelimit input = some (payload,tail) ∧
      ∃ t ≤ 3*input.length+2, runSteps machine.step t (Turing.initList machine input) = some (cfg .done none tail [] payload)) ∨
    (BitstringEncoding.undelimit input = none ∧ ∃ t ≤ input.length+1, ∃ scratch,
      runSteps machine.step t (Turing.initList machine input) = some (cfg .reject none [] scratch [])) := by
  cases h : BitstringEncoding.undelimit input with
  | none =>
    right
    obtain ⟨t,ht,scratch,hr⟩ := invalid_run input [] [] none h
    exact ⟨rfl,t,ht,scratch,by simpa [initial_eq] using hr⟩
  | some p =>
    left
    rcases p with ⟨payload,tail⟩
    have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound input payload tail h
    refine ⟨payload,tail,rfl,3*payload.length+2,?_,?_⟩
    · have hs : payload.length ≤ input.length := by
        rw [← he,List.length_append,BitstringEncoding.length_delimit]
        omega
      omega
    · rw [← he]
      exact valid_run payload tail

theorem valid_run_of_decode (input payload tail : List Bool)
    (h : BitstringEncoding.undelimit input = some (payload,tail)) :
    runSteps machine.step (3*payload.length+2) (Turing.initList machine input) =
      some (cfg .done none tail [] payload) := by
  rw [← Shared.ComplexityBridge.CNFWitness.undelimit_sound input payload tail h]
  exact valid_run payload tail

namespace Fixtures
/-- An incomplete marker is rejected, rather than parsed as an empty block. -/
example : (runSteps machine.step 2 (Turing.initList machine [true])).map
    (fun c => (match c.l with | some .reject => true | _ => false,c.stk .scratch)) = some (true,([] : List Bool)) := by
  change (Option.map (fun c => (match c.l with | some .reject => true | _ => false,c.stk .scratch))
    (runSteps machine.step 2 (Turing.initList machine [true])) : Option (Bool × List Bool)) = _
  decide

/-- A payload with no final delimiter is rejected after storing its bit. -/
example : (runSteps machine.step 3 (Turing.initList machine [true,false])).map
    (fun c => (match c.l with | some .reject => true | _ => false,c.stk .scratch)) = some (true,[false]) := by
  change (Option.map (fun c => (match c.l with | some .reject => true | _ => false,c.stk .scratch))
    (runSteps machine.step 3 (Turing.initList machine [true,false])) : Option (Bool × List Bool)) = _
  decide

/-- A valid block preserves a nonempty suffix and restores the payload order. -/
example : (runSteps machine.step 5 (Turing.initList machine [true,true,false,false,true])).map
    (fun c => (match c.l with | some .done => true | _ => false,c.stk .input,c.stk .payload)) =
      some (true,[false,true],[true]) := by
  change (Option.map (fun c => (match c.l with | some .done => true | _ => false,c.stk .input,c.stk .payload))
    (runSteps machine.step 5 (Turing.initList machine [true,true,false,false,true])) : Option (Bool × List Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2Undelimit
