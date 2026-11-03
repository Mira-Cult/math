import Shared.ComplexityBridge.CNFChoiceCounted
import Shared.ComplexityBridge.TM2ComposeEncoded
import Shared.ComplexityBridge.TM2ListCodec

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Close the counted choice loop's finite-machine boundary: initialize with
raw fuel as input, erase the final index, reverse the output accumulator, and
halt with the exact canonical clause encoding. -/
namespace Shared.ComplexityBridge.CNFChoiceOutput
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev C := Shared.ComplexityBridge.CNFChoiceCounted.machine
abbrev Key := Shared.ComplexityBridge.CNFChoiceCounted.Key
abbrev CL := Shared.ComplexityBridge.CNFChoiceCounted.Label
abbrev State := Shared.ComplexityBridge.CNFChoiceCounted.State
inductive Phase where | clear | output deriving DecidableEq
instance : Fintype Phase := Fintype.ofList [.clear,.output] (by intro l; cases l <;> simp)
abbrev Label := CL ⊕ Phase

def embed (q : C.Cfg) : Cfg (fun _ : Key => Bool) Label State := ⟨q.l.map Sum.inl,q.var,q.stk⟩

def lift : C.Stmt → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push j f (lift q)
  | .peek j f q => .peek j f (lift q)
  | .pop j f q => .pop j f (lift q)
  | .load f q => .load f (lift q)
  | .branch f q r => .branch f (lift q) (lift r)
  | .goto f => .goto (Sum.inl ∘ f)
  | .halt => .halt

theorem lift_aux (q : C.Stmt) (v : State) (S : Key → List Bool) :
    stepAux (lift q) v S = embed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl (.inl .done) => .load (fun _ => (none,none)) (.goto (fun _ => .inr .clear))
  | .inl l => lift (Shared.ComplexityBridge.CNFChoiceCounted.program l)
  | .inr .clear => .pop (.inl .index) (fun _ h => (h,none))
      (.branch (fun v => v.1.isSome) (.goto (fun _ => .inr .clear)) (.goto (fun _ => .inr .output)))
  | .inr .output => .pop (.inl .accumulator) (fun _ h => (h,none))
      (.branch (fun v => v.1.isSome)
        (.push (.inr ()) (fun v => v.1.getD false) (.goto (fun _ => .inr .output)))
        (.load (fun _ => (none,none)) .halt))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inr ()
  k₁ := .inr ()
  Γ := fun _ => Bool
  Λ := Label
  main := .inl (.inl .guard)
  σ := State
  initialState := (none,none)
  m := program

def terminal (q : C.Cfg) : Prop := q.l = some (.inl .done)
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : C.Cfg) (h : terminal q) : C.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inl Shared.ComplexityBridge.CNFChoiceCounted.Control.done) at h
    subst l
    rfl

theorem core_step (q : C.Cfg) (h : ¬terminal q) :
    machine.step (embed q) = (C.step q).map embed := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | inl l =>
        cases l with
        | done => exact False.elim (h rfl)
        | guard =>
          change some (stepAux (lift (Shared.ComplexityBridge.CNFChoiceCounted.program _)) v S) = _
          rw [lift_aux]; rfl
      | inr l =>
        change some (stepAux (lift (Shared.ComplexityBridge.CNFChoiceCounted.program _)) v S) = _
        rw [lift_aux]; rfl

theorem initial_eq (fuel : List Bool) :
    Turing.initList machine fuel = embed (Shared.ComplexityBridge.CNFChoiceCounted.cfg (.inl .guard) none none [] [] [] fuel) := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,embed,Shared.ComplexityBridge.CNFChoiceCounted.cfg,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Turing.initList]
  | inr k => cases k <;> simp [machine,embed,Shared.ComplexityBridge.CNFChoiceCounted.cfg,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Turing.initList]

def cfg (l : Phase) (v : Option Bool) (bits acc out : List Bool) : machine.Cfg :=
  ⟨some (.inr l),(v,none),Shared.ComplexityBridge.CNFChoiceCounted.stackVals bits [] acc out⟩

theorem dispatch (bits acc : List Bool) :
    machine.step (embed (Shared.ComplexityBridge.CNFChoiceCounted.cfg (.inl .done) none none bits [] acc [])) =
      some (cfg .clear none bits acc []) := by
  change some (Cfg.mk _ _ _) = _
  congr 2

theorem clear_cons (v : Option Bool) (b : Bool) (bits acc out : List Bool) :
    machine.step (cfg .clear v (b::bits) acc out) = some (cfg .clear (some b) bits acc out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Function.update]
  | inr k => cases k <;> simp [machine,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Function.update]

theorem clear_nil (v : Option Bool) (acc out : List Bool) :
    machine.step (cfg .clear v [] acc out) = some (cfg .output none [] acc out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Function.update]
  | inr k => cases k <;> simp [machine,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Function.update]

theorem output_cons (v : Option Bool) (b : Bool) (acc out : List Bool) :
    machine.step (cfg .output v [] (b::acc) out) = some (cfg .output (some b) [] acc (b::out)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Function.update]
  | inr k => cases k <;> simp [machine,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Function.update]

theorem output_nil (v : Option Bool) (out : List Bool) :
    machine.step (cfg .output v [] [] out) = some (Turing.haltList machine out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Function.update,Turing.haltList]
  | inr k => cases k <;> simp [machine,Shared.ComplexityBridge.CNFChoiceCounted.stackVals,Function.update,Turing.haltList]

theorem clear_run (bits acc out : List Bool) (v : Option Bool) :
    runSteps machine.step (bits.length+1) (cfg .clear v bits acc out) = some (cfg .output none [] acc out) := by
  induction bits generalizing v with
  | nil => exact clear_nil v acc out
  | cons b bits ih =>
    rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,clear_cons]
    exact ih (some b)

theorem output_run (acc out : List Bool) (v : Option Bool) :
    runSteps machine.step (acc.length+1) (cfg .output v [] acc out) =
      some (Turing.haltList machine (acc.reverse++out)) := by
  induction acc generalizing out v with
  | nil => exact output_nil v out
  | cons b acc ih =>
    rw [List.length_cons,show acc.length+1+1 = (acc.length+1)+1 by omega,runSteps_front,output_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::out) (some b)

/-- The actual finite machine starts with only raw tokens on its input and
halts with the exact serialized zero-start choice clause. -/
theorem run_fuel (fuel : List Bool) :
    ∃ t ≤ fuel.length*(8*fuel.length+18)+4,
      runSteps machine.step t (Turing.initList machine fuel) =
        some (Turing.haltList machine (BitstringEncoding.bitEncode
          (Shared.ComplexityBridge.CNFDisjunction.choices 0 fuel.length))) := by
  let f := Shared.ComplexityBridge.CNFChoiceBitCosts.loop fuel [] []
  let fin := Shared.ComplexityBridge.CNFChoiceCounted.cfg (.inl .done) none none f.1.1 [] f.1.2 []
  have hl := Shared.ComplexityBridge.CNFChoiceCounted.loop_run fuel [] [] none
  obtain ⟨n,hn,hr⟩ := hl
  simp only [List.length_nil,Nat.zero_add] at hn
  change runSteps C.step n (Shared.ComplexityBridge.CNFChoiceCounted.cfg (.inl .guard) none none [] [] [] fuel) = some fin at hr
  obtain ⟨d,hd,he⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    C.step machine.step embed terminal stable core_step n _ fin (by rfl) hr
  have hbits : f.1.1.length ≤ fuel.length := by
    have h := Shared.ComplexityBridge.CNFChoiceBitCosts.loop_bits_length fuel [] []
    simpa [f] using h
  have hacc : f.1.2.length ≤ fuel.length*(4*fuel.length+9) := by
    have h := Shared.ComplexityBridge.CNFChoiceBitCosts.loop_acc_length fuel [] []
    simpa [f] using h
  have hout : f.1.2.reverse = BitstringEncoding.bitEncode
      (Shared.ComplexityBridge.CNFDisjunction.choices 0 fuel.length) := by
    have h := Shared.ComplexityBridge.CNFChoiceBitCosts.loop_correct fuel 0 []
    simpa [f] using congrArg List.reverse h
  refine ⟨d+1+(f.1.1.length+1)+(f.1.2.length+1),?_,?_⟩
  · have hm : fuel.length*(4*fuel.length+8)+fuel.length+
      fuel.length*(4*fuel.length+9) = fuel.length*(8*fuel.length+18) := by ring
    omega
  · rw [initial_eq,show d+1+(f.1.1.length+1)+(f.1.2.length+1) =
        d+(1+((f.1.1.length+1)+(f.1.2.length+1))) by omega,runSteps_add,he]
    change runSteps machine.step (1+((f.1.1.length+1)+(f.1.2.length+1))) (embed fin) = _
    rw [Nat.add_comm 1 _,runSteps_front,dispatch]
    change runSteps machine.step ((f.1.1.length+1)+(f.1.2.length+1)) (cfg .clear none f.1.1 f.1.2 []) = _
    rw [runSteps_add,clear_run]
    simpa [hout] using output_run f.1.2 [] none

def choiceClause (fuel : List Bool) : Shared.ComplexityBridge.CNF.Clause :=
  Shared.ComplexityBridge.CNFDisjunction.choices 0 fuel.length

noncomputable def rawTimeMachine : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : Shared.ComplexityBridge.CNF.Clause → List Bool) choiceClause where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X*(Polynomial.C 8*Polynomial.X+Polynomial.C 18)+Polynomial.C 4
  outputsFun fuel := by
    classical
    let t := Nat.find (run_fuel fuel)
    have ht := (Nat.find_spec (run_fuel fuel)).1
    have hr := (Nat.find_spec (run_fuel fuel)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine (fuel.map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (choiceClause fuel)).map id))
      simpa [choiceClause] using hr
    · simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq] using ht

/-- Canonical list input is explicitly decoded before the counted loop. -/
theorem choiceClause_isPolyTime : ComplexityTheory.IsPolyTime choiceClause := by
  exact Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : Shared.ComplexityBridge.CNF.Clause → List Bool)
    id choiceClause Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine rawTimeMachine

namespace Fixtures
example : ∃ t ≤ 4, runSteps machine.step t (Turing.initList machine []) =
    some (Turing.haltList machine (BitstringEncoding.bitEncode
      (Shared.ComplexityBridge.CNFDisjunction.choices 0 0))) := by
  simpa using run_fuel []
example : ∃ t ≤ 72, runSteps machine.step t (Turing.initList machine [true,false]) =
    some (Turing.haltList machine (BitstringEncoding.bitEncode
      (Shared.ComplexityBridge.CNFDisjunction.choices 0 2))) := by
  simpa using run_fuel [true,false]
end Fixtures
end Shared.ComplexityBridge.CNFChoiceOutput
