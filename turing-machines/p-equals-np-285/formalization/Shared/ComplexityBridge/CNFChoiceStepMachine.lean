import Shared.ComplexityBridge.CNFChoiceEmitter
import Shared.ComplexityBridge.TM2UnaryTransfer

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Join the finite selector emitter to an in-place binary incrementer. One
positive, bounded segment realizes the entire bit-level choice-generator step.
The iteration controller and input/output loading remain separate. -/
namespace Shared.ComplexityBridge.CNFChoiceStepMachine
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.Codes.BitTableValidation (increment)
abbrev E := Shared.ComplexityBridge.CNFChoiceEmitter.machine
abbrev Key := Shared.ComplexityBridge.CNFChoiceEmitter.Stack
abbrev ELabel := Shared.ComplexityBridge.CNFChoiceEmitter.Label
inductive IncLabel where | carry | copy | restore deriving DecidableEq
instance : Fintype IncLabel := Fintype.ofList [.carry,.copy,.restore] (by intro l; cases l <;> simp)
abbrev Label := ELabel ⊕ IncLabel

def embed (q : E.Cfg) : Cfg (fun _ : Key => Bool) Label (Option Bool) :=
  ⟨q.l.map Sum.inl,q.var,q.stk⟩

def lift : E.Stmt → Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .push j f q => .push j f (lift q)
  | .peek j f q => .peek j f (lift q)
  | .pop j f q => .pop j f (lift q)
  | .load f q => .load f (lift q)
  | .branch f q r => .branch f (lift q) (lift r)
  | .goto f => .goto (Sum.inl ∘ f)
  | .halt => .halt

theorem lift_aux (q : E.Stmt) (v : Option Bool) (S : Key → List Bool) :
    stepAux (lift q) v S = embed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .inl .done => .load (fun _ => none) (.goto (fun _ => .inr .carry))
  | .inl l => lift (Shared.ComplexityBridge.CNFChoiceEmitter.program l)
  | .inr .carry => .pop .index (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true)
          (.push .scratch (fun _ => false) (.goto (fun _ => .inr .carry)))
          (.push .scratch (fun _ => true) (.goto (fun _ => .inr .copy))))
        (.push .scratch (fun _ => true) (.goto (fun _ => .inr .restore))))
  | .inr .copy => .pop .index (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false) (.goto (fun _ => .inr .copy)))
        (.goto (fun _ => .inr .restore)))
  | .inr .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .index (fun v => v.getD false) (.goto (fun _ => .inr .restore)))
        (.load (fun _ => none) (.goto (fun _ => .inl .start))))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .index
  k₁ := .accumulator
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .start
  σ := Option Bool
  initialState := none
  m := program

def terminal (q : E.Cfg) : Prop := q.l = some .done
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : E.Cfg) (h : terminal q) : E.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.CNFChoiceEmitter.Label.done at h
    subst l
    rfl

theorem emitter_step (q : E.Cfg) (h : ¬terminal q) :
    machine.step (embed q) = (E.step q).map embed := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | start | emit | restore =>
        change some (stepAux (lift (Shared.ComplexityBridge.CNFChoiceEmitter.program _)) v S) = _
        rw [lift_aux]; rfl

def cfg (l : Label) (v : Option Bool) (bits scratch acc : List Bool) : machine.Cfg :=
  ⟨some l,v,Shared.ComplexityBridge.CNFChoiceEmitter.stackVals bits scratch acc⟩

theorem dispatch (bits acc : List Bool) :
    machine.step (embed (Shared.ComplexityBridge.CNFChoiceEmitter.cfg .done none bits [] acc)) =
      some (cfg (.inr .carry) none bits [] acc) := rfl

theorem carry_one (v : Option Bool) (bits scratch acc : List Bool) :
    machine.step (cfg (.inr .carry) v (true::bits) scratch acc) =
      some (cfg (.inr .carry) (some true) bits (false::scratch) acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFChoiceEmitter.stackVals,Function.update]

theorem carry_zero (v : Option Bool) (bits scratch acc : List Bool) :
    machine.step (cfg (.inr .carry) v (false::bits) scratch acc) =
      some (cfg (.inr .copy) (some false) bits (true::scratch) acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFChoiceEmitter.stackVals,Function.update]

theorem carry_nil (v : Option Bool) (scratch acc : List Bool) :
    machine.step (cfg (.inr .carry) v [] scratch acc) =
      some (cfg (.inr .restore) none [] (true::scratch) acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFChoiceEmitter.stackVals,Function.update]

theorem copy_cons (v : Option Bool) (b : Bool) (bits scratch acc : List Bool) :
    machine.step (cfg (.inr .copy) v (b::bits) scratch acc) =
      some (cfg (.inr .copy) (some b) bits (b::scratch) acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFChoiceEmitter.stackVals,Function.update]

theorem copy_nil (v : Option Bool) (scratch acc : List Bool) :
    machine.step (cfg (.inr .copy) v [] scratch acc) =
      some (cfg (.inr .restore) none [] scratch acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFChoiceEmitter.stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (bits scratch acc : List Bool) :
    machine.step (cfg (.inr .restore) v bits (b::scratch) acc) =
      some (cfg (.inr .restore) (some b) (b::bits) scratch acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFChoiceEmitter.stackVals,Function.update]

theorem restore_nil (v : Option Bool) (bits acc : List Bool) :
    machine.step (cfg (.inr .restore) v bits [] acc) =
      some (cfg (.inl .start) none bits [] acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFChoiceEmitter.stackVals,Function.update]

theorem copy_run (bits scratch acc : List Bool) (v : Option Bool) :
    runSteps machine.step (bits.length+1) (cfg (.inr .copy) v bits scratch acc) =
      some (cfg (.inr .restore) none [] (bits.reverse++scratch) acc) := by
  induction bits generalizing scratch v with
  | nil => exact copy_nil v scratch acc
  | cons b bits ih =>
    rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,copy_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem carry_run (bits scratch acc : List Bool) (v : Option Bool) :
    runSteps machine.step (bits.length+1) (cfg (.inr .carry) v bits scratch acc) =
      some (cfg (.inr .restore) none [] ((increment bits).1.reverse++scratch) acc) := by
  induction bits generalizing scratch v with
  | nil => simpa [increment,runSteps] using carry_nil v scratch acc
  | cons b bits ih =>
    cases b with
    | false =>
      rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,carry_zero]
      simpa [increment,List.reverse_cons,List.append_assoc] using copy_run bits (true::scratch) acc (some false)
    | true =>
      rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,carry_one]
      simpa [increment,List.reverse_cons,List.append_assoc] using ih (false::scratch) (some true)

theorem restore_run (scratch bits acc : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg (.inr .restore) v bits scratch acc) =
      some (cfg (.inl .start) none (scratch.reverse++bits) [] acc) := by
  induction scratch generalizing bits v with
  | nil => exact restore_nil v bits acc
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::bits) (some b)

theorem increment_run (bits acc : List Bool) :
    runSteps machine.step (bits.length+1+((increment bits).1.length+1))
      (cfg (.inr .carry) none bits [] acc) =
      some (cfg (.inl .start) none (increment bits).1 [] acc) := by
  rw [runSteps_add,carry_run]
  simpa using restore_run (increment bits).1.reverse [] acc none

/-- One complete iteration is a single finite table, and realizes both the
updated index and accumulated output of the executable bit-level step. -/
theorem step_run (bits acc : List Bool) :
    ∃ d, 0 < d ∧ d ≤ 4*bits.length+7 ∧
      runSteps machine.step d (cfg (.inl .start) none bits [] acc) =
        some (cfg (.inl .start) none
          (Shared.ComplexityBridge.CNFChoiceBitCosts.step bits acc).1.1 []
          (Shared.ComplexityBridge.CNFChoiceBitCosts.step bits acc).1.2) := by
  let fin := Shared.ComplexityBridge.CNFChoiceEmitter.cfg .done none bits []
    ((Shared.ComplexityBridge.CNFChoiceBitCosts.block bits).reverse++acc)
  have he := Shared.ComplexityBridge.CNFChoiceEmitter.run bits acc
  change runSteps E.step (2*bits.length+3)
    (Shared.ComplexityBridge.CNFChoiceEmitter.cfg .start none bits [] acc) = some fin at he
  obtain ⟨d,hd,hr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    E.step machine.step embed terminal stable emitter_step _ _ fin (by rfl) he
  let j := bits.length+1+((increment bits).1.length+1)
  have hj : j ≤ 2*bits.length+3 := by
    have h := Shared.Codes.BitTableValidation.increment_length bits
    dsimp [j]; omega
  refine ⟨d+1+j,by omega,by omega,?_⟩
  change runSteps machine.step (d+1+j)
    (embed (Shared.ComplexityBridge.CNFChoiceEmitter.cfg .start none bits [] acc)) = _
  rw [show d+1+j = d+(1+j) by omega,runSteps_add,hr]
  change runSteps machine.step (1+j) (embed fin) = _
  rw [Nat.add_comm 1 j,runSteps_front,dispatch]
  simpa [j,Shared.ComplexityBridge.CNFChoiceBitCosts.step_correct] using
    increment_run bits ((Shared.ComplexityBridge.CNFChoiceBitCosts.block bits).reverse++acc)

/-- Any finite number of iterations is covered by the same table. The token
list controls only the theorem's number of iterations; a concrete machine
that reads and consumes those tokens is still to be connected. -/
theorem iterate_run (fuel bits acc : List Bool) :
    ∃ d, fuel.length ≤ d ∧ d ≤ fuel.length*(4*(bits.length+fuel.length)+7) ∧
      runSteps machine.step d (cfg (.inl .start) none bits [] acc) =
        some (cfg (.inl .start) none
          (Shared.ComplexityBridge.CNFChoiceBitCosts.loop fuel bits acc).1.1 []
          (Shared.ComplexityBridge.CNFChoiceBitCosts.loop fuel bits acc).1.2) := by
  induction fuel generalizing bits acc with
  | nil => exact ⟨0,by simp,by simp,by simp [runSteps,Shared.ComplexityBridge.CNFChoiceBitCosts.loop]⟩
  | cons b fuel ih =>
    let s := Shared.ComplexityBridge.CNFChoiceBitCosts.step bits acc
    obtain ⟨d,hpos,hd,hr⟩ := step_run bits acc
    obtain ⟨e,helo,he,hs⟩ := ih s.1.1 s.1.2
    have hlen : s.1.1.length ≤ bits.length+1 := by
      have h := Shared.Codes.BitTableValidation.increment_length bits
      simpa [s,Shared.ComplexityBridge.CNFChoiceBitCosts.step_correct] using h
    have hupper : 4*(s.1.1.length+fuel.length)+7 ≤ 4*(bits.length+(fuel.length+1))+7 := by omega
    have hm := Nat.mul_le_mul_left fuel.length hupper
    refine ⟨d+e,by simp only [List.length_cons]; omega,?_,?_⟩
    · simp only [List.length_cons]
      have heq : (fuel.length+1)*(4*(bits.length+(fuel.length+1))+7) =
          fuel.length*(4*(bits.length+(fuel.length+1))+7) +
            (4*(bits.length+(fuel.length+1))+7) := by ring
      rw [heq]
      omega
    · rw [runSteps_add,hr]
      change runSteps machine.step e (cfg (.inl .start) none s.1.1 [] s.1.2) = _
      simpa only [Shared.ComplexityBridge.CNFChoiceBitCosts.loop] using hs

/-- The iteration boundaries agree with the pinned serialized choice clause,
with the accumulated bytes held in reverse order. -/
theorem choices_run (fuel : List Bool) (start : Nat) :
    ∃ d ≤ fuel.length*(4*(start.bits.length+fuel.length)+7),
      runSteps machine.step d (cfg (.inl .start) none start.bits [] []) =
        some (cfg (.inl .start) none (start+fuel.length).bits []
          (BitstringEncoding.bitEncode
            (Shared.ComplexityBridge.CNFDisjunction.choices start fuel.length)).reverse) := by
  obtain ⟨d,_,hd,hr⟩ := iterate_run fuel start.bits []
  refine ⟨d,hd,?_⟩
  simpa [Shared.ComplexityBridge.CNFChoiceBitCosts.loop_final_index,
    Shared.ComplexityBridge.CNFChoiceBitCosts.loop_correct] using hr

namespace Fixtures
example : ∃ d ≤ 30, runSteps machine.step d (cfg (.inl .start) none [] [] []) =
    some (cfg (.inl .start) none (2 : Nat).bits []
      (BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.choices 0 2)).reverse) := by
  simpa using choices_run [true,true] 0
end Fixtures

end Shared.ComplexityBridge.CNFChoiceStepMachine
