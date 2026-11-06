import Shared.ComplexityBridge.TM2GenericDiagonal
import Shared.ComplexityBridge.TM2Undelimit
import Shared.ComplexityBridge.TM2MapSizeBounds

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Project the first component of any canonical pair using a finite TM2.
The suffix is explicitly erased before the machine halts. -/
namespace Shared.ComplexityBridge.TM2PairFirst
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev U := Shared.ComplexityBridge.TM2Undelimit.machine
abbrev Key := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev ULabel := Shared.ComplexityBridge.TM2Undelimit.Label
abbrev Label := ULabel ⊕ Unit

def embed (q : U.Cfg) : Cfg (fun _ : Key => Bool) Label (Option Bool) := ⟨q.l.map Sum.inl,q.var,q.stk⟩

def lift : U.Stmt → Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .push j f q => .push j f (lift q)
  | .peek j f q => .peek j f (lift q)
  | .pop j f q => .pop j f (lift q)
  | .load f q => .load f (lift q)
  | .branch f q r => .branch f (lift q) (lift r)
  | .goto f => .goto (Sum.inl ∘ f)
  | .halt => .halt

theorem lift_aux (q : U.Stmt) (v : Option Bool) (S : Key → List Bool) :
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
  | .inl .done => .goto (fun _ => .inr ())
  | .inl l => lift (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr () => .pop .input (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .inr ())) (.load (fun _ => none) .halt))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .input
  k₁ := .payload
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .header
  σ := Option Bool
  initialState := none
  m := program

def terminal (q : U.Cfg) : Prop := q.l = some .done
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : U.Cfg) (h : terminal q) : U.step q = some q :=
  Shared.ComplexityBridge.TM2ListAppend.stable q h

theorem loader_step (q : U.Cfg) (h : ¬terminal q) :
    machine.step (embed q) = (U.step q).map embed := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | header | data | restore | reject =>
        change some (stepAux (lift (Shared.ComplexityBridge.TM2Undelimit.program _)) v S) = _
        rw [lift_aux]; rfl

theorem initial_eq (input : List Bool) : Turing.initList machine input = embed (Turing.initList U input) := by rfl

def cfg (v : Option Bool) (input payload : List Bool) : machine.Cfg :=
  ⟨some (.inr ()),v,Shared.ComplexityBridge.TM2Undelimit.stackVals input [] payload⟩

theorem dispatch (a b : List Bool) :
    machine.step (embed (Shared.ComplexityBridge.TM2Undelimit.cfg .done none b [] a)) = some (cfg none b a) := by
  change some (Cfg.mk _ _ _) = _
  congr 2

theorem clear_cons (v : Option Bool) (b : Bool) (input payload : List Bool) :
    machine.step (cfg v (b::input) payload) = some (cfg (some b) input payload) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem clear_nil (v : Option Bool) (payload : List Bool) :
    machine.step (cfg v [] payload) = some (Turing.haltList machine payload) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update,Turing.haltList,machine]

theorem clear_run (input payload : List Bool) (v : Option Bool) :
    runSteps machine.step (input.length+1) (cfg v input payload) = some (Turing.haltList machine payload) := by
  induction input generalizing v with
  | nil => exact clear_nil v payload
  | cons b input ih =>
    rw [List.length_cons,show input.length+1+1 = (input.length+1)+1 by omega,runSteps_front,clear_cons]
    exact ih (some b)

theorem run_bits (a b : List Bool) :
    ∃ t ≤ 3*a.length+b.length+4,
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.delimit a++b)) =
        some (Turing.haltList machine a) := by
  let fin := Shared.ComplexityBridge.TM2Undelimit.cfg .done none b [] a
  have hl := Shared.ComplexityBridge.TM2Undelimit.valid_run a b
  change runSteps U.step (3*a.length+2) (Turing.initList U (BitstringEncoding.delimit a++b)) = some fin at hl
  obtain ⟨d,hd,hr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    U.step machine.step embed terminal stable loader_step _ _ fin (by rfl) hl
  refine ⟨d+1+(b.length+1),by omega,?_⟩
  rw [initial_eq,show d+1+(b.length+1) = d+(1+(b.length+1)) by omega,runSteps_add,hr]
  change runSteps machine.step (1+(b.length+1)) (embed fin) = _
  rw [Nat.add_comm 1 _,runSteps_front,dispatch]
  exact clear_run b a none

def first {α β : Type} (p : α × β) : α := p.1

noncomputable def timeMachine {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : α × β → List Bool)
      (BitstringEncoding.bitEncode : α → List Bool) (first (α := α) (β := β)) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2*Polynomial.X+Polynomial.C 2
  outputsFun p := by
    classical
    rcases p with ⟨x,y⟩
    let a := BitstringEncoding.bitEncode x
    let b := BitstringEncoding.bitEncode y
    have hi : BitstringEncoding.bitEncode (x,y) = BitstringEncoding.delimit a++b := rfl
    let t := Nat.find (run_bits a b)
    have ht := (Nat.find_spec (run_bits a b)).1
    have hr := (Nat.find_spec (run_bits a b)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode (x,y)).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (first (x,y))).map id))
      simpa [hi,first] using hr
    · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,hi,
        List.length_append,BitstringEncoding.length_delimit]
      omega

theorem first_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    ComplexityTheory.IsPolyTime (first (α := α) (β := β)) := ⟨timeMachine⟩

/-- A polynomial-time context-and-item operation can return its result with
its original context, using explicit copying, projection and pair swap. -/
theorem withContext_isPolyTime {κ α β : Type} [BitstringEncoding κ] [BitstringEncoding α] [BitstringEncoding β]
    (F : κ × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (fun p : κ × α => (p.1,F p)) := by
  let keep : κ × α → β × (κ × α) := fun p => (F p,p)
  let project : β × (κ × α) → β × κ := fun p => (p.1,first p.2)
  let flip : β × κ → κ × β := Shared.ComplexityBridge.TM2PairSwap.swap
  have hk : ComplexityTheory.IsPolyTime keep := Shared.ComplexityBridge.TM2GenericDiagonal.withInput_isPolyTime F hF
  have hp : ComplexityTheory.IsPolyTime project :=
    Shared.ComplexityBridge.TM2PairSwap.mapSecond_isPolyTime first first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime flip := Shared.ComplexityBridge.TM2PairSwap.swap_isPolyTime
  have h₁ := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp keep project hk hp
  have h₂ := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp (fun p => project (keep p)) flip h₁ hs
  simpa [keep,project,flip,first,Shared.ComplexityBridge.TM2PairSwap.swap] using h₂

theorem guard_with_context_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × Shared.ComplexityBridge.CNF.Clause =>
      (p.1,Shared.ComplexityBridge.CNFDisjunction.guardClause p.1 p.2)) :=
  withContext_isPolyTime _ Shared.ComplexityBridge.TM2PairSwap.guardClause_isPolyTime

/-- One fixed item machine returns the unchanged index with the guarded
clause, with a uniform clock in the full encoded formula request. -/
theorem guard_with_context_item_run :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (f : Shared.ComplexityBridge.CNF.Formula) (c : Shared.ComplexityBridge.CNF.Clause), c ∈ f →
        ∃ n ≤ p.eval (BitstringEncoding.bitEncode (i,f)).length,
          runSteps core.tm.step n
            (Turing.initList core.tm ((BitstringEncoding.bitEncode (i,c)).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode
            (i,Shared.ComplexityBridge.CNFDisjunction.guardClause i c)).map core.outputAlphabet.symm)) :=
  Shared.ComplexityBridge.TM2MapSizeBounds.context_item_run _ guard_with_context_isPolyTime

namespace Fixtures
example : ∃ t ≤ 4, runSteps machine.step t (Turing.initList machine [false]) =
    some (Turing.haltList machine []) := by
  simpa [BitstringEncoding.delimit] using run_bits [] []
example : ∃ t ≤ 8, runSteps machine.step t (Turing.initList machine [true,true,false,false]) =
    some (Turing.haltList machine [true]) := by
  simpa [BitstringEncoding.delimit] using run_bits [true] [false]
end Fixtures
end Shared.ComplexityBridge.TM2PairFirst
