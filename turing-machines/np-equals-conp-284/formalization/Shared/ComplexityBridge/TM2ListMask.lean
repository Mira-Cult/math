import Shared.ComplexityBridge.TM2TagInput

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2ListMask
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
inductive Stack where | input | scratch | output deriving DecidableEq
inductive Label where | start | scan | restore | discard deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.start,.scan,.restore,.discard] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .start => .pop .input (fun _ h => h)
      (.pop .input (fun _ h => h)
        (.branch (fun v => v == some true)
          (.pop .input (fun _ h => h) (.goto (fun _ => .scan)))
          (.pop .input (fun _ h => h) (.goto (fun _ => .discard)))))
  | .scan => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan))) (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome (.push .output (fun v => v.getD false) (.goto (fun _ => .restore))) (.load (fun _ => none) .halt))
  | .discard => .pop .input (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .discard))
        (.load (fun _ => none) .halt))

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

theorem start_bit (b : Bool) (input : List Bool) :
    machine.step (cfg .start none (true::b::false::input) [] []) =
      some (cfg (if b then .scan else .discard) (some false) input [] []) := by
  cases b <;>
    change some (Cfg.mk _ _ (Function.update (Function.update (Function.update
      (stackVals (true::_::false::input) [] []) .input (_::false::input)) .input (false::input)) .input input)) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

theorem discard_cons (flag : Option Bool) (b : Bool) (input : List Bool) :
    machine.step (cfg .discard flag (b::input) [] []) = some (cfg .discard (some b) input [] []) := by
  change some (Cfg.mk _ _ (Function.update (stackVals (b::input) [] []) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem discard_nil (flag : Option Bool) :
    machine.step (cfg .discard flag [] [] []) = some (Turing.haltList machine []) := by
  change some (Cfg.mk none (none : Option Bool) (Function.update (stackVals [] [] []) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine]

theorem discard_loop (input : List Bool) (flag : Option Bool) :
    runSteps machine.step (input.length+1) (cfg .discard flag input [] []) = some (Turing.haltList machine []) := by
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
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine]

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
  congr 1; funext k; cases k <;> simp [machine,stackVals,Turing.initList]

/-- A flagged canonical list returns the list on true and the empty list on
false. Both branches consume all input and leave all non-output stacks empty. -/
def mask {α : Type} (p : Bool × List α) : List α := if p.1 then p.2 else []

theorem run_bits (b : Bool) (input : List Bool) :
    ∃ t ≤ 2*input.length+3,
      runSteps machine.step t (Turing.initList machine (true::b::false::input)) =
        some (Turing.haltList machine (if b then input else [])) := by
  cases b with
  | false =>
    refine ⟨input.length+2,by omega,?_⟩
    rw [initial_eq,show input.length+2 = (input.length+1)+1 by omega,runSteps_front,start_bit]
    exact discard_loop input (some false)
  | true =>
    obtain ⟨v,hs⟩ := scan_loop input [] [] (some false)
    simp only [List.append_nil] at hs
    have hr := restore_loop input.reverse [] none
    simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
    refine ⟨2*input.length+3,by omega,?_⟩
    have hn : 2*input.length+3 = 1+(input.length+(1+(input.length+1))) := by omega
    rw [initial_eq,hn,runSteps_add]
    change (machine.step (cfg .start none (true::true::false::input) [] [])).bind _ = _
    rw [start_bit]
    change runSteps machine.step (input.length+(1+(input.length+1))) (cfg .scan (some false) input [] []) = _
    rw [runSteps_add,hs]
    change runSteps machine.step (1+(input.length+1)) (cfg .scan v [] input.reverse []) = _
    rw [runSteps_add]
    change (machine.step (cfg .scan v [] input.reverse [])).bind _ = _
    rw [scan_nil]
    exact hr

noncomputable def timeMachine {α : Type} [BitstringEncoding α] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : Bool × List α → List Bool)
      (BitstringEncoding.bitEncode : List α → List Bool) mask where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2*Polynomial.X+Polynomial.C 3
  outputsFun p := by
    rcases p with ⟨b,xs⟩
    let bits := BitstringEncoding.bitEncode xs
    have hi : BitstringEncoding.bitEncode (b,xs) = true::b::false::bits := by
      change BitstringEncoding.delimit [b] ++ bits = _
      simp [BitstringEncoding.delimit]
    let t := Classical.choose (run_bits b bits)
    have ht := (Classical.choose_spec (run_bits b bits)).1
    have hr := (Classical.choose_spec (run_bits b bits)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode (b,xs)).map id))) =
          some (Turing.haltList machine ((BitstringEncoding.bitEncode (mask (b,xs))).map id))
      rw [List.map_id,List.map_id,hi]
      have hnil : BitstringEncoding.bitEncode ([] : List α) = [] := rfl
      cases b <;> simpa [mask,bits,hnil,t] using hr
    · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,hi,List.length_cons]
      omega

theorem mask_isPolyTime {α : Type} [BitstringEncoding α] :
    ComplexityTheory.IsPolyTime (mask (α := α)) := ⟨timeMachine⟩

namespace Fixtures
example : (runSteps machine.step 3 (Turing.initList machine [true,false,false,true])).map
    (fun q => (q.l.isNone,q.stk .output)) = some (true,[]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .output))
    (runSteps machine.step 3 (Turing.initList machine [true,false,false,true])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 5 (Turing.initList machine [true,true,false,true])).map
    (fun q => (q.l.isNone,q.stk .output)) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .output))
    (runSteps machine.step 5 (Turing.initList machine [true,true,false,true])) : Option (Bool × List Bool)) = _
  decide
example : mask (false, [1,2]) = ([] : List Nat) := rfl
example : mask (true, [1,2]) = ([1,2] : List Nat) := rfl
end Fixtures
end Shared.ComplexityBridge.TM2ListMask
