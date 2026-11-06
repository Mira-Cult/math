import Shared.ComplexityBridge.CNFChoiceStepMachine

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! A token-driven finite TM2 choice loop. Each token triggers one emitted
selector block and one binary increment. Input stacks are explicit; final
output remains reversed and later loading/cleanup are separate. -/
namespace Shared.ComplexityBridge.CNFChoiceCounted
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.Codes.BitTableValidation (increment)
abbrev E := Shared.ComplexityBridge.CNFChoiceEmitter.machine
abbrev EK := Shared.ComplexityBridge.CNFChoiceEmitter.Stack
abbrev EL := Shared.ComplexityBridge.CNFChoiceEmitter.Label
abbrev IL := Shared.ComplexityBridge.CNFChoiceStepMachine.IncLabel
inductive Control where | guard | done deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.guard,.done] (by intro l; cases l <;> simp)
abbrev Key := EK ⊕ Unit
abbrev Label := Control ⊕ (EL ⊕ IL)
abbrev State := Option Bool × Option Bool

def stackVals (bits scratch acc fuel : List Bool) : Key → List Bool
  | .inl .index => bits | .inl .scratch => scratch | .inl .accumulator => acc | .inr _ => fuel

def embed (q : E.Cfg) (marker : Option Bool) (fuel : List Bool) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),(q.var,marker),fun k => match k with | .inl j => q.stk j | .inr _ => fuel⟩

def lift : E.Stmt → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (.inl j) (fun v => f v.1) (lift q)
  | .peek j f q => .peek (.inl j) (fun v h => (f v.1 h,v.2)) (lift q)
  | .pop j f q => .pop (.inl j) (fun v h => (f v.1 h,v.2)) (lift q)
  | .load f q => .load (fun v => (f v.1,v.2)) (lift q)
  | .branch f q r => .branch (fun v => f v.1) (lift q) (lift r)
  | .goto f => .goto (fun v => .inr (.inl (f v.1)))
  | .halt => .halt

theorem lift_aux (q : E.Stmt) (v marker : Option Bool) (S : EK → List Bool) (fuel : List Bool) :
    stepAux (lift q) (v,marker) (fun k => match k with | .inl j => S j | .inr _ => fuel) =
      embed (stepAux q v S) marker fuel := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih =>
    simp only [lift,stepAux]
    have hu : Function.update (fun k : Key => match k with | .inl j => S j | .inr _ => fuel)
        (.inl j) (S j).tail = (fun k => match k with | .inl i => (Function.update S j (S j).tail) i | .inr _ => fuel) := by
      funext k; cases k with
      | inl k => by_cases h : k = j <;> simp [Function.update,h]
      | inr k => simp [Function.update]
    rw [hu]
    exact ih _ _
  | push j f q ih =>
    simp only [lift,stepAux]
    have hu : Function.update (fun k : Key => match k with | .inl j => S j | .inr _ => fuel)
        (.inl j) (f v::S j) = (fun k => match k with | .inl i => (Function.update S j (f v::S j)) i | .inr _ => fuel) := by
      funext k; cases k with
      | inl k => by_cases h : k = j <;> simp [Function.update,h]
      | inr k => simp [Function.update]
    rw [hu]
    exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .guard => .pop (.inr ()) (fun v h => (v.1,h))
      (.branch (fun v => v.2.isSome)
        (.load (fun v => (none,v.2)) (.goto (fun _ => .inr (.inl .start))))
        (.load (fun _ => (none,none)) (.goto (fun _ => .inl .done))))
  | .inl .done => .goto (fun _ => .inl .done)
  | .inr (.inl .done) => .load (fun v => (none,v.2)) (.goto (fun _ => .inr (.inr .carry)))
  | .inr (.inl l) => lift (Shared.ComplexityBridge.CNFChoiceEmitter.program l)
  | .inr (.inr .carry) => .pop (.inl .index) (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.branch (fun v => v.1 == some true)
          (.push (.inl .scratch) (fun _ => false) (.goto (fun _ => .inr (.inr .carry))))
          (.push (.inl .scratch) (fun _ => true) (.goto (fun _ => .inr (.inr .copy)))))
        (.push (.inl .scratch) (fun _ => true) (.goto (fun _ => .inr (.inr .restore)))))
  | .inr (.inr .copy) => .pop (.inl .index) (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.push (.inl .scratch) (fun v => v.1.getD false) (.goto (fun _ => .inr (.inr .copy))))
        (.goto (fun _ => .inr (.inr .restore))))
  | .inr (.inr .restore) => .pop (.inl .scratch) (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.push (.inl .index) (fun v => v.1.getD false) (.goto (fun _ => .inr (.inr .restore))))
        (.load (fun v => (none,v.2)) (.goto (fun _ => .inl .guard))))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inl .index
  k₁ := .inl .accumulator
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .guard
  σ := State
  initialState := (none,none)
  m := program

def cfg (l : Label) (v marker : Option Bool) (bits scratch acc fuel : List Bool) : machine.Cfg :=
  ⟨some l,(v,marker),stackVals bits scratch acc fuel⟩

theorem guard_cons (v marker : Option Bool) (bits acc fuel : List Bool) (b : Bool) :
    machine.step (cfg (.inl .guard) v marker bits [] acc (b::fuel)) =
      some (embed (Shared.ComplexityBridge.CNFChoiceEmitter.cfg .start none bits [] acc) (some b) fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [stackVals,embed,Shared.ComplexityBridge.CNFChoiceEmitter.cfg,Shared.ComplexityBridge.CNFChoiceEmitter.stackVals,Function.update]
  | inr k => cases k <;> simp [stackVals,embed,Shared.ComplexityBridge.CNFChoiceEmitter.cfg,Function.update]

theorem guard_nil (v marker : Option Bool) (bits acc : List Bool) :
    machine.step (cfg (.inl .guard) v marker bits [] acc []) =
      some (cfg (.inl .done) none none bits [] acc []) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]

def terminal (q : E.Cfg) : Prop := q.l = some .done
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : E.Cfg) (h : terminal q) : E.step q = some q :=
  Shared.ComplexityBridge.CNFChoiceStepMachine.stable q h

theorem emitter_step (marker : Option Bool) (fuel : List Bool) (q : E.Cfg) (h : ¬terminal q) :
    machine.step (embed q marker fuel) = (E.step q).map (fun q => embed q marker fuel) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | start | emit | restore =>
        change some (stepAux (lift (Shared.ComplexityBridge.CNFChoiceEmitter.program _)) (v,marker)
          (fun k => match k with | .inl j => S j | .inr _ => fuel)) = _
        rw [lift_aux]; rfl

theorem dispatch (bits acc fuel : List Bool) (marker : Option Bool) :
    machine.step (embed (Shared.ComplexityBridge.CNFChoiceEmitter.cfg .done none bits [] acc) marker fuel) =
      some (cfg (.inr (.inr .carry)) none marker bits [] acc fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [stackVals,embed,Shared.ComplexityBridge.CNFChoiceEmitter.cfg,Shared.ComplexityBridge.CNFChoiceEmitter.stackVals]
  | inr k => cases k <;> rfl

theorem carry_one (v marker : Option Bool) (bits scratch acc fuel : List Bool) :
    machine.step (cfg (.inr (.inr .carry)) v marker (true::bits) scratch acc fuel) =
      some (cfg (.inr (.inr .carry)) (some true) marker bits (false::scratch) acc fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]

theorem carry_zero (v marker : Option Bool) (bits scratch acc fuel : List Bool) :
    machine.step (cfg (.inr (.inr .carry)) v marker (false::bits) scratch acc fuel) =
      some (cfg (.inr (.inr .copy)) (some false) marker bits (true::scratch) acc fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]

theorem carry_nil (v marker : Option Bool) (scratch acc fuel : List Bool) :
    machine.step (cfg (.inr (.inr .carry)) v marker [] scratch acc fuel) =
      some (cfg (.inr (.inr .restore)) none marker [] (true::scratch) acc fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]

theorem copy_cons (v marker : Option Bool) (b : Bool) (bits scratch acc fuel : List Bool) :
    machine.step (cfg (.inr (.inr .copy)) v marker (b::bits) scratch acc fuel) =
      some (cfg (.inr (.inr .copy)) (some b) marker bits (b::scratch) acc fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]

theorem copy_nil (v marker : Option Bool) (scratch acc fuel : List Bool) :
    machine.step (cfg (.inr (.inr .copy)) v marker [] scratch acc fuel) =
      some (cfg (.inr (.inr .restore)) none marker [] scratch acc fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]

theorem restore_cons (v marker : Option Bool) (b : Bool) (bits scratch acc fuel : List Bool) :
    machine.step (cfg (.inr (.inr .restore)) v marker bits (b::scratch) acc fuel) =
      some (cfg (.inr (.inr .restore)) (some b) marker (b::bits) scratch acc fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]

theorem restore_nil (v marker : Option Bool) (bits acc fuel : List Bool) :
    machine.step (cfg (.inr (.inr .restore)) v marker bits [] acc fuel) =
      some (cfg (.inl .guard) none marker bits [] acc fuel) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,stackVals,Function.update,Sum.inl.injEq]

theorem copy_run (bits scratch acc fuel : List Bool) (v marker : Option Bool) :
    runSteps machine.step (bits.length+1) (cfg (.inr (.inr .copy)) v marker bits scratch acc fuel) =
      some (cfg (.inr (.inr .restore)) none marker [] (bits.reverse++scratch) acc fuel) := by
  induction bits generalizing scratch v with
  | nil => exact copy_nil v marker scratch acc fuel
  | cons b bits ih =>
    rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,copy_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem carry_run (bits scratch acc fuel : List Bool) (v marker : Option Bool) :
    runSteps machine.step (bits.length+1) (cfg (.inr (.inr .carry)) v marker bits scratch acc fuel) =
      some (cfg (.inr (.inr .restore)) none marker [] ((increment bits).1.reverse++scratch) acc fuel) := by
  induction bits generalizing scratch v with
  | nil => simpa [increment,runSteps] using carry_nil v marker scratch acc fuel
  | cons b bits ih =>
    cases b with
    | false =>
      rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,carry_zero]
      simpa [increment,List.reverse_cons,List.append_assoc] using copy_run bits (true::scratch) acc fuel (some false) marker
    | true =>
      rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,carry_one]
      simpa [increment,List.reverse_cons,List.append_assoc] using ih (false::scratch) (some true)

theorem restore_run (scratch bits acc fuel : List Bool) (v marker : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg (.inr (.inr .restore)) v marker bits scratch acc fuel) =
      some (cfg (.inl .guard) none marker (scratch.reverse++bits) [] acc fuel) := by
  induction scratch generalizing bits v with
  | nil => exact restore_nil v marker bits acc fuel
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::bits) (some b)

theorem increment_run (bits acc fuel : List Bool) (marker : Option Bool) :
    runSteps machine.step (bits.length+1+((increment bits).1.length+1))
      (cfg (.inr (.inr .carry)) none marker bits [] acc fuel) =
      some (cfg (.inl .guard) none marker (increment bits).1 [] acc fuel) := by
  rw [runSteps_add,carry_run]
  simpa using restore_run (increment bits).1.reverse [] acc fuel none marker

/-- Consuming one actual token and executing its generator step has a
positive finite duration bounded by the current binary index length. -/
theorem cycle (b : Bool) (fuel bits acc : List Bool) (marker : Option Bool) :
    ∃ d, 0 < d ∧ d ≤ 4*bits.length+8 ∧
      runSteps machine.step d (cfg (.inl .guard) none marker bits [] acc (b::fuel)) =
        some (cfg (.inl .guard) none (some b)
          (Shared.ComplexityBridge.CNFChoiceBitCosts.step bits acc).1.1 []
          (Shared.ComplexityBridge.CNFChoiceBitCosts.step bits acc).1.2 fuel) := by
  let fin := Shared.ComplexityBridge.CNFChoiceEmitter.cfg .done none bits []
    ((Shared.ComplexityBridge.CNFChoiceBitCosts.block bits).reverse++acc)
  have he := Shared.ComplexityBridge.CNFChoiceEmitter.run bits acc
  change runSteps E.step (2*bits.length+3)
    (Shared.ComplexityBridge.CNFChoiceEmitter.cfg .start none bits [] acc) = some fin at he
  obtain ⟨d,hd,hr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    E.step machine.step (fun q => embed q (some b) fuel) terminal stable (emitter_step (some b) fuel) _ _ fin (by rfl) he
  let j := bits.length+1+((increment bits).1.length+1)
  have hj : j ≤ 2*bits.length+3 := by
    have h := Shared.Codes.BitTableValidation.increment_length bits
    dsimp [j]; omega
  refine ⟨1+d+1+j,by omega,by omega,?_⟩
  rw [show 1+d+1+j = 1+(d+(1+j)) by omega,runSteps_add]
  change (machine.step (cfg (.inl .guard) none marker bits [] acc (b::fuel))).bind _ = _
  rw [guard_cons]
  change runSteps machine.step (d+(1+j)) _ = _
  rw [runSteps_add,hr]
  change runSteps machine.step (1+j) (embed fin (some b) fuel) = _
  rw [Nat.add_comm 1 j,runSteps_front,dispatch]
  simpa [j,Shared.ComplexityBridge.CNFChoiceBitCosts.step_correct] using
    increment_run bits ((Shared.ComplexityBridge.CNFChoiceBitCosts.block bits).reverse++acc) fuel (some b)

/-- The concrete table consumes all tokens and reaches `done`; the proof
counts all guard, emitter, dispatch and increment blocks. -/
theorem loop_run (fuel bits acc : List Bool) (marker : Option Bool) :
    ∃ d ≤ fuel.length*(4*(bits.length+fuel.length)+8)+1,
      runSteps machine.step d (cfg (.inl .guard) none marker bits [] acc fuel) =
        some (cfg (.inl .done) none none
          (Shared.ComplexityBridge.CNFChoiceBitCosts.loop fuel bits acc).1.1 []
          (Shared.ComplexityBridge.CNFChoiceBitCosts.loop fuel bits acc).1.2 []) := by
  induction fuel generalizing bits acc marker with
  | nil => exact ⟨1,by simp,by simpa [runSteps,Shared.ComplexityBridge.CNFChoiceBitCosts.loop] using guard_nil none marker bits acc⟩
  | cons b fuel ih =>
    let s := Shared.ComplexityBridge.CNFChoiceBitCosts.step bits acc
    obtain ⟨d,_,hd,hr⟩ := cycle b fuel bits acc marker
    obtain ⟨e,he,hs⟩ := ih s.1.1 s.1.2 (some b)
    have hlen : s.1.1.length ≤ bits.length+1 := by
      have h := Shared.Codes.BitTableValidation.increment_length bits
      simpa [s,Shared.ComplexityBridge.CNFChoiceBitCosts.step_correct] using h
    have hupper : 4*(s.1.1.length+fuel.length)+8 ≤ 4*(bits.length+(fuel.length+1))+8 := by omega
    have hm := Nat.mul_le_mul_left fuel.length hupper
    refine ⟨d+e,?_,?_⟩
    · simp only [List.length_cons]
      have heq : (fuel.length+1)*(4*(bits.length+(fuel.length+1))+8)+1 =
          fuel.length*(4*(bits.length+(fuel.length+1))+8) +
            (4*(bits.length+(fuel.length+1))+8)+1 := by ring
      rw [heq]
      omega
    · rw [runSteps_add,hr]
      change runSteps machine.step e (cfg (.inl .guard) none (some b) s.1.1 [] s.1.2 fuel) = _
      simpa only [Shared.ComplexityBridge.CNFChoiceBitCosts.loop] using hs

/-- Actual fuel consumption produces the exact reverse-serialized clause at
an explicit done boundary. -/
theorem choices_run (fuel : List Bool) (start : Nat) :
    ∃ d ≤ fuel.length*(4*(start.bits.length+fuel.length)+8)+1,
      runSteps machine.step d (cfg (.inl .guard) none none start.bits [] [] fuel) =
        some (cfg (.inl .done) none none (start+fuel.length).bits []
          (BitstringEncoding.bitEncode
            (Shared.ComplexityBridge.CNFDisjunction.choices start fuel.length)).reverse []) := by
  obtain ⟨d,hd,hr⟩ := loop_run fuel start.bits [] none
  refine ⟨d,hd,?_⟩
  simpa [Shared.ComplexityBridge.CNFChoiceBitCosts.loop_final_index,
    Shared.ComplexityBridge.CNFChoiceBitCosts.loop_correct] using hr

namespace Fixtures
example : ∃ d ≤ 1, runSteps machine.step d (cfg (.inl .guard) none none [] [] [] []) =
    some (cfg (.inl .done) none none [] [] [] []) := by
  simpa [Shared.ComplexityBridge.CNFChoiceBitCosts.loop] using loop_run [] [] [] none
example : ∃ d ≤ 33, runSteps machine.step d (cfg (.inl .guard) none none [] [] [] [true,false]) =
    some (cfg (.inl .done) none none (2 : Nat).bits []
      (BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.choices 0 2)).reverse []) := by
  simpa using choices_run [true,false] 0
end Fixtures

end Shared.ComplexityBridge.CNFChoiceCounted
