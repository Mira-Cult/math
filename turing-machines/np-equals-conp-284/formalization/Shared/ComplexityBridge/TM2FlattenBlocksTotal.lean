import Shared.ComplexityBridge.TM2FlattenBlocks
import Shared.ComplexityBridge.TM2GenericStackBound

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2FlattenBlocksTotal
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Stack := Shared.ComplexityBridge.TM2FlattenBlocks.Stack
abbrev Source := Shared.ComplexityBridge.TM2FlattenBlocks.machine
abbrev SourceLabel := Shared.ComplexityBridge.TM2FlattenBlocks.Label
abbrev SourceState := Shared.ComplexityBridge.TM2FlattenBlocks.State
abbrev Label := SourceLabel ⊕ Unit
abbrev State := SourceState ⊕ Option Bool

def sourceState : State → SourceState | .inl v => v | .inr _ => (none,false)
def clearState : State → Option Bool | .inl _ => none | .inr v => v

def sourceEmbed (q : Source.Cfg) : Cfg (fun _ : Stack => Bool) Label State :=
  ⟨q.l.map Sum.inl,.inl q.var,q.stk⟩

def liftSource : Stmt (fun _ : Stack => Bool) SourceLabel SourceState → Stmt (fun _ : Stack => Bool) Label State
  | .push j f q => .push j (fun v => f (sourceState v)) (liftSource q)
  | .peek j f q => .peek j (fun v h => .inl (f (sourceState v) h)) (liftSource q)
  | .pop j f q => .pop j (fun v h => .inl (f (sourceState v) h)) (liftSource q)
  | .load f q => .load (fun v => .inl (f (sourceState v))) (liftSource q)
  | .branch f q r => .branch (fun v => f (sourceState v)) (liftSource q) (liftSource r)
  | .goto f => .goto (fun v => .inl (f (sourceState v)))
  | .halt => .halt

theorem liftSource_aux (q : Stmt (fun _ : Stack => Bool) SourceLabel SourceState)
    (v : SourceState) (S : Stack → List Bool) :
    stepAux (liftSource q) (.inl v) S = sourceEmbed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftSource,stepAux,sourceState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .inl .done => .push .output (fun _ => true) (.load (fun _ => .inl (none,false)) .halt)
  | .inl .reject => .load (fun _ => .inr none) (.goto (fun _ => .inr ()))
  | .inl l => liftSource (Shared.ComplexityBridge.TM2FlattenBlocks.program l)
  | .inr () => .pop .scratch (fun _ h => .inr h)
      (.branch (fun v => (clearState v).isSome) (.goto (fun _ => .inr ()))
        (.push .output (fun _ => false) (.load (fun _ => .inl (none,false)) .halt)))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .header
  σ := State
  initialState := .inl (none,false)
  m := program

def terminal (q : Source.Cfg) : Prop := q.l = some .done ∨ q.l = some .reject
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _

theorem source_stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some .done ∨ l = some .reject at h
    rcases h with h | h <;> subst l <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem source_step (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (sourceEmbed q) = (Source.step q).map sourceEmbed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | done => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | header | data | restore =>
        change some (stepAux (liftSource (Shared.ComplexityBridge.TM2FlattenBlocks.program _)) (.inl v) S) = _
        rw [liftSource_aux]; rfl

theorem initial_eq (input : List Bool) : Turing.initList machine input = sourceEmbed (Turing.initList Source input) := rfl

def clearCfg (v : Option Bool) (scratch : List Bool) : machine.Cfg :=
  ⟨some (.inr ()),.inr v,Shared.ComplexityBridge.TM2FlattenBlocks.stackVals [] scratch []⟩

theorem success_dispatch (blocks : List (List Bool)) :
    machine.step (sourceEmbed (Shared.ComplexityBridge.TM2FlattenBlocks.cfg .done none false [] []
      (blocks.flatten))) =
      some (Turing.haltList machine (true::blocks.flatten)) := by
  change some (Cfg.mk (none : Option Label) (.inl (none,false) : State)
    (Function.update (Shared.ComplexityBridge.TM2FlattenBlocks.stackVals [] [] (blocks.flatten))
      .output (true::blocks.flatten))) = _
  congr 1; congr 1; funext k; cases k <;>
    simp [Shared.ComplexityBridge.TM2FlattenBlocks.stackVals,Function.update,Turing.haltList,machine] <;> rfl

theorem reject_dispatch (scratch : List Bool) :
    machine.step (sourceEmbed (Shared.ComplexityBridge.TM2FlattenBlocks.cfg .reject none true [] scratch [])) =
      some (clearCfg none scratch) := rfl

theorem clear_cons (v : Option Bool) (b : Bool) (scratch : List Bool) :
    machine.step (clearCfg v (b::scratch)) = some (clearCfg (some b) scratch) := by
  change some (Cfg.mk (some (Sum.inr ()) : Option Label) (.inr (some b) : State)
    (Function.update (Shared.ComplexityBridge.TM2FlattenBlocks.stackVals [] (b::scratch) []) .scratch scratch)) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2FlattenBlocks.stackVals,Function.update]

theorem clear_nil (v : Option Bool) : machine.step (clearCfg v []) = some (Turing.haltList machine [false]) := by
  change some (Cfg.mk (none : Option Label) (.inl (none,false) : State)
    (Function.update (Function.update (Shared.ComplexityBridge.TM2FlattenBlocks.stackVals [] [] []) .scratch [])
      .output [false])) = _
  congr 1; congr 1; funext k; cases k <;>
    simp [Shared.ComplexityBridge.TM2FlattenBlocks.stackVals,Function.update,Turing.haltList,machine] <;> rfl

theorem clear_run (scratch : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (clearCfg v scratch) = some (Turing.haltList machine [false]) := by
  induction scratch generalizing v with
  | nil => exact clear_nil v
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,clear_cons]
    exact ih (some b)

/-- A tagged result: false means malformed; true is followed by the
concatenated decoded block payloads. Boundaries are intentionally not retained. -/
def encodeResult : Option (List (List Bool)) → List Bool
  | none => [false]
  | some blocks => true::blocks.flatten

def decodeResult (bits : List Bool) : List Bool := encodeResult (BitstringEncoding.undelimitBlocks bits)

noncomputable def timePolynomial : Polynomial Nat :=
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  Polynomial.C (D+6)*Polynomial.X + Polynomial.C (D+7)

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = (Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source+6)*n +
      (Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source+7) := by simp [timePolynomial]

set_option backward.isDefEq.respectTransparency false in
/-- The parser and both cleanup paths reach the actual output convention in a
single fixed linear polynomial, for every raw Boolean input. -/
theorem total_run (input : List Bool) :
    ∃ t ≤ timePolynomial.eval input.length,
      runSteps machine.step t (Turing.initList machine input) = some (Turing.haltList machine (decodeResult input)) := by
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  rcases Shared.ComplexityBridge.TM2FlattenBlocks.parse_progress input with hv | hi
  · obtain ⟨blocks,hdecode,n,hn,hr⟩ := hv
    let q := Shared.ComplexityBridge.TM2FlattenBlocks.cfg .done none false [] [] (blocks.flatten)
    change runSteps Source.step n (Turing.initList Source input) = some q at hr
    obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      Source.step machine.step sourceEmbed terminal source_stable source_step n (Turing.initList Source input) q (Or.inl rfl) hr
    refine ⟨a+1,?_,?_⟩
    · rw [timePolynomial_eval]
      change a+1 ≤ (D+6)*input.length+(D+7)
      rw [Nat.add_mul]
      omega
    · rw [decodeResult,hdecode]
      change runSteps machine.step (a+1) (Turing.initList machine input) = some (Turing.haltList machine (true::blocks.flatten))
      rw [initial_eq,runSteps_add,har]
      change machine.step (sourceEmbed q) = _
      exact success_dispatch blocks
  · obtain ⟨hdecode,n,hn,scratch,hr⟩ := hi
    let q := Shared.ComplexityBridge.TM2FlattenBlocks.cfg .reject none true [] scratch []
    change runSteps Source.step n (Turing.initList Source input) = some q at hr
    have hstack := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length Source input n q hr .scratch
    have hs : scratch.length ≤ input.length+n*D := by
      simpa [q,Shared.ComplexityBridge.TM2FlattenBlocks.cfg,Shared.ComplexityBridge.TM2FlattenBlocks.stackVals,D] using hstack
    have hm : n*D ≤ (input.length+1)*D := Nat.mul_le_mul_right D hn
    obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      Source.step machine.step sourceEmbed terminal source_stable source_step n (Turing.initList Source input) q (Or.inr rfl) hr
    refine ⟨a+1+(scratch.length+1),?_,?_⟩
    · rw [timePolynomial_eval]
      change a+1+(scratch.length+1) ≤ (D+6)*input.length+(D+7)
      rw [Nat.add_mul,Nat.mul_comm D input.length]
      simp only [Nat.add_mul,Nat.one_mul] at hm
      omega
    · rw [decodeResult,hdecode]
      change runSteps machine.step (a+1+(scratch.length+1)) (Turing.initList machine input) =
        some (Turing.haltList machine [false])
      rw [initial_eq,show a+1+(scratch.length+1) = a+((scratch.length+1)+1) by omega,runSteps_add,har]
      change runSteps machine.step ((scratch.length+1)+1) (sourceEmbed q) = _
      rw [runSteps_front,reject_dispatch]
      change runSteps machine.step (scratch.length+1) (clearCfg none scratch) = _
      exact clear_run scratch none

set_option backward.isDefEq.respectTransparency false in
/-- This is an actual polynomial-time TM2 witness with raw bit-list input and
output boundaries. It does not assert the Google canonical list encoding. -/
noncomputable def rawTimeMachine :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) decodeResult where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun input := by
    let h := total_run input
    let n := Classical.choose h
    have hn := Classical.choose_spec h
    refine ⟨⟨n,?_⟩,hn.1⟩
    have hr := hn.2
    rw [runSteps_iterate] at hr
    change (fun o => o.bind machine.step)^[n] (some (Turing.initList machine (input.map id))) =
      some (Turing.haltList machine ((decodeResult input).map id))
    rw [List.map_id,List.map_id]
    exact hr

namespace Fixtures
/-- Empty input is a successful empty block list, with its success tag. -/
example : (runSteps machine.step 3 (Turing.initList machine [])).map
    (fun c => (c.l.isNone,c.stk .output)) = some (true,[true]) := by
  change (Option.map (fun c => (c.l.isNone,c.stk .output))
    (runSteps machine.step 3 (Turing.initList machine [])) : Option (Bool × List Bool)) = _
  decide

/-- An incomplete second block is cleaned up and returns the false tag. -/
example : (runSteps machine.step 5 (Turing.initList machine [false,true])).map
    (fun c => (c.l.isNone,c.stk .output,c.stk .scratch)) = some (true,[false],([] : List Bool)) := by
  change (Option.map (fun c => (c.l.isNone,c.stk .output,c.stk .scratch))
    (runSteps machine.step 5 (Turing.initList machine [false,true])) : Option (Bool × List Bool × List Bool)) = _
  decide

/-- A valid two-block result includes the success tag and all payloads. -/
example : (runSteps machine.step 11 (Turing.initList machine
    (Shared.ComplexityBridge.TM2FlattenBlocks.framed [[],[true,false]]))).map
    (fun c => (c.l.isNone,c.stk .output)) =
      some (true,[true,true,false]) := by
  change (Option.map (fun c => (c.l.isNone,c.stk .output))
    (runSteps machine.step 11 (Turing.initList machine
      (Shared.ComplexityBridge.TM2FlattenBlocks.framed [[],[true,false]]))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2FlattenBlocksTotal
