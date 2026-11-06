import Shared.ComplexityBridge.TM2ListAppend
import Shared.ComplexityBridge.TM2TypedPairMap
import Shared.ComplexityBridge.CNFEvenClause

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Swap canonical pair components with a finite TM2, charging parsing and
re-serialization. The component encodings are copied as bits. -/
namespace Shared.ComplexityBridge.TM2PairSwap
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNFBinaryPairAdd

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .done => .load (fun _ => .inr (true,none,none)) (.goto (fun _ => .inr .readLeft))
  | .inl l => liftU (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr .readLeft => .pop .left (fun _ h => .inr (true,h,none))
      (.branch (fun v => (aState v).2.1.isSome)
        (.push .scratch (fun v => (aState v).2.1.getD false) (.goto (fun _ => .inr .readLeft)))
        (.goto (fun _ => .inr .restore)))
  | .inr .readRight => .pop .right (fun _ h => .inr (false,h,none))
      (.branch (fun v => (aState v).2.1.isSome)
        (.push .scratch (fun v => (aState v).2.1.getD false) (.goto (fun _ => .inr .readRight)))
        (.goto (fun _ => .inr .restore)))
  | .inr .restore => .pop .scratch (fun v h => .inr ((aState v).1,h,none))
      (.branch (fun v => (aState v).2.1.isSome)
        (.branch (fun v => (aState v).1)
          (.push .output (fun v => (aState v).2.1.getD false) (.goto (fun _ => .inr .restore)))
          (.push .output (fun v => (aState v).2.1.getD false)
            (.push .output (fun _ => true) (.goto (fun _ => .inr .restore)))))
        (.branch (fun v => (aState v).1)
          (.push .output (fun _ => false) (.goto (fun _ => .inr .readRight)))
          (.load (fun _ => .inl none) .halt)))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .right
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .header
  σ := State
  initialState := .inl none
  m := program

def terminal (q : U.Cfg) : Prop := q.l = some .done
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : U.Cfg) (h : terminal q) : U.step q = some q :=
  Shared.ComplexityBridge.TM2ListAppend.stable q h

theorem loader_step (q : U.Cfg) (h : ¬terminal q) :
    machine.step (uEmbed [] q) = (U.step q).map (uEmbed []) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | header | data | restore | reject =>
        change some (stepAux (liftU (Shared.ComplexityBridge.TM2Undelimit.program _)) (.inl v) (uStacks S [])) = _
        rw [liftU_aux]; rfl

theorem initial_eq (bits : List Bool) :
    Turing.initList machine bits = uEmbed [] (Turing.initList U bits) := by
  exact Shared.ComplexityBridge.CNFBinaryPairAdd.initial_eq bits

def cfg (l : AL) (flag : Bool) (v : Option Bool) (a b scratch out : List Bool) : machine.Cfg :=
  ⟨some (.inr l),.inr (flag,v,none),Shared.ComplexityBridge.CNFBinaryAdd.stackVals a b scratch out⟩

theorem dispatch (a b : List Bool) :
    machine.step (uEmbed [] (Shared.ComplexityBridge.TM2Undelimit.cfg .done none b [] a)) =
      some (cfg .readLeft true none a b [] []) := by
  change some (Cfg.mk _ _ _) = _
  congr 2

theorem left_cons (v : Option Bool) (x : Bool) (a b scratch out : List Bool) :
    machine.step (cfg .readLeft true v (x::a) b scratch out) =
      some (cfg .readLeft true (some x) a b (x::scratch) out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem left_nil (v : Option Bool) (b scratch out : List Bool) :
    machine.step (cfg .readLeft true v [] b scratch out) = some (cfg .restore true none [] b scratch out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem right_cons (flag : Bool) (v : Option Bool) (x : Bool) (b scratch out : List Bool) :
    machine.step (cfg .readRight flag v [] (x::b) scratch out) =
      some (cfg .readRight false (some x) [] b (x::scratch) out) := by
  cases flag <;> change some (Cfg.mk _ _ _) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem right_nil (flag : Bool) (v : Option Bool) (scratch out : List Bool) :
    machine.step (cfg .readRight flag v [] [] scratch out) = some (cfg .restore false none [] [] scratch out) := by
  cases flag <;> change some (Cfg.mk _ _ _) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem restore_true_cons (v : Option Bool) (x : Bool) (b scratch out : List Bool) :
    machine.step (cfg .restore true v [] b (x::scratch) out) =
      some (cfg .restore true (some x) [] b scratch (x::out)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem restore_true_nil (v : Option Bool) (b out : List Bool) :
    machine.step (cfg .restore true v [] b [] out) = some (cfg .readRight true none [] b [] (false::out)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem restore_false_cons (v : Option Bool) (x : Bool) (scratch out : List Bool) :
    machine.step (cfg .restore false v [] [] (x::scratch) out) =
      some (cfg .restore false (some x) [] [] scratch (true::x::out)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem restore_false_nil (v : Option Bool) (out : List Bool) :
    machine.step (cfg .restore false v [] [] [] out) = some (Turing.haltList machine out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState,Turing.haltList,machine]

theorem left_run (a b scratch out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step a.length (cfg .readLeft true v a b scratch out) =
      some (cfg .readLeft true v' [] b (a.reverse++scratch) out) := by
  induction a generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons x a ih =>
    obtain ⟨v',hr⟩ := ih (x::scratch) (some x)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,left_cons]
    simpa [List.reverse_cons,List.append_assoc] using hr

theorem right_run (b scratch out : List Bool) (flag : Bool) (v : Option Bool) :
    ∃ flag' v', runSteps machine.step b.length (cfg .readRight flag v [] b scratch out) =
      some (cfg .readRight flag' v' [] [] (b.reverse++scratch) out) := by
  induction b generalizing scratch flag v with
  | nil => exact ⟨flag,v,by simp [runSteps]⟩
  | cons x b ih =>
    obtain ⟨flag',v',hr⟩ := ih (x::scratch) false (some x)
    refine ⟨flag',v',?_⟩
    rw [List.length_cons,runSteps_front,right_cons]
    simpa [List.reverse_cons,List.append_assoc] using hr

theorem restore_true_run (scratch b out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore true v [] b scratch out) =
      some (cfg .restore true v' [] b [] (scratch.reverse++out)) := by
  induction scratch generalizing out v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons x scratch ih =>
    obtain ⟨v',hr⟩ := ih (x::out) (some x)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_true_cons]
    simpa [List.reverse_cons,List.append_assoc] using hr

theorem restore_false_run (scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore false v [] [] scratch out) =
      some (Turing.haltList machine (Shared.ComplexityBridge.CNFLiteralConstructor.framedBits scratch.reverse++out)) := by
  induction scratch generalizing out v with
  | nil => simpa [runSteps,Shared.ComplexityBridge.CNFLiteralConstructor.framedBits] using restore_false_nil v out
  | cons x scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_false_cons]
    simpa [Shared.ComplexityBridge.CNFLiteralConstructor.framedBits,List.reverse_cons,List.flatMap_append,List.append_assoc] using ih (true::x::out) (some x)

theorem first_phase (a b : List Bool) :
    runSteps machine.step (2*a.length+2) (cfg .readLeft true none a b [] []) =
      some (cfg .readRight true none [] b [] (false::a)) := by
  obtain ⟨v,hs⟩ := left_run a b [] [] none
  simp only [List.append_nil] at hs
  obtain ⟨w,hr⟩ := restore_true_run a.reverse b [] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  have hc : 2*a.length+2 = a.length+1+(a.length+1) := by omega
  rw [hc,runSteps_add,runSteps_add,hs]
  change runSteps machine.step 1 (cfg .readLeft true v [] b a.reverse []) >>= _ = _
  rw [show runSteps machine.step 1 (cfg .readLeft true v [] b a.reverse []) =
    machine.step (cfg .readLeft true v [] b a.reverse []) by rfl,left_nil]
  change runSteps machine.step (a.length+1) (cfg .restore true none [] b a.reverse []) = _
  rw [runSteps_add,hr]
  exact restore_true_nil w b a

theorem second_phase (a b : List Bool) :
    runSteps machine.step (2*b.length+2) (cfg .readRight true none [] b [] (false::a)) =
      some (Turing.haltList machine (BitstringEncoding.delimit b++a)) := by
  obtain ⟨flag,v,hs⟩ := right_run b [] (false::a) true none
  simp only [List.append_nil] at hs
  have hr := restore_false_run b.reverse (false::a) none
  simp only [List.reverse_reverse,List.length_reverse] at hr
  have hc : 2*b.length+2 = b.length+1+(b.length+1) := by omega
  rw [hc,runSteps_add,runSteps_add,hs]
  change runSteps machine.step 1 (cfg .readRight flag v [] [] b.reverse (false::a)) >>= _ = _
  rw [show runSteps machine.step 1 (cfg .readRight flag v [] [] b.reverse (false::a)) =
    machine.step (cfg .readRight flag v [] [] b.reverse (false::a)) by rfl,right_nil]
  simpa [Shared.ComplexityBridge.CNFLiteralConstructor.delimit_prefix,List.append_assoc] using hr

theorem run_bits (a b : List Bool) :
    ∃ t ≤ 5*a.length+2*b.length+7,
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.delimit a ++ b)) =
        some (Turing.haltList machine (BitstringEncoding.delimit b ++ a)) := by
  let fin := Shared.ComplexityBridge.TM2Undelimit.cfg .done none b [] a
  have hl := Shared.ComplexityBridge.TM2Undelimit.valid_run a b
  change runSteps U.step (3*a.length+2) (Turing.initList U (BitstringEncoding.delimit a ++ b)) = some fin at hl
  obtain ⟨d,hd,he⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    U.step machine.step (uEmbed []) terminal stable loader_step _ _ fin (by rfl) hl
  refine ⟨d+1+(2*a.length+2)+(2*b.length+2),by omega,?_⟩
  rw [initial_eq,show d+1+(2*a.length+2)+(2*b.length+2) =
    d+(1+((2*a.length+2)+(2*b.length+2))) by omega,runSteps_add,he]
  change runSteps machine.step (1+((2*a.length+2)+(2*b.length+2))) (uEmbed [] fin) = _
  rw [Nat.add_comm 1 _,runSteps_front,dispatch]
  change runSteps machine.step ((2*a.length+2)+(2*b.length+2)) (cfg .readLeft true none a b [] []) = _
  rw [runSteps_add,first_phase]
  exact second_phase a b

def swap {α β : Type} (p : α × β) : β × α := (p.2,p.1)

noncomputable def timeMachine {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : α × β → List Bool)
      (BitstringEncoding.bitEncode : β × α → List Bool) (swap (α := α) (β := β)) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3*Polynomial.X+Polynomial.C 4
  outputsFun p := by
    classical
    rcases p with ⟨x,y⟩
    let a := BitstringEncoding.bitEncode x
    let b := BitstringEncoding.bitEncode y
    have hi : BitstringEncoding.bitEncode (x,y) = BitstringEncoding.delimit a ++ b := by rfl
    have ho : BitstringEncoding.bitEncode (swap (x,y)) = BitstringEncoding.delimit b ++ a := by rfl
    let t := Nat.find (run_bits a b)
    have ht := (Nat.find_spec (run_bits a b)).1
    have hr := (Nat.find_spec (run_bits a b)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode (x,y)).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (swap (x,y))).map id))
      simpa [hi,ho] using hr
    · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,hi,
        List.length_append,BitstringEncoding.length_delimit]
      omega

theorem swap_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    ComplexityTheory.IsPolyTime (swap (α := α) (β := β)) := ⟨timeMachine⟩

/-- Applying a polynomial-time function to the second pair component is
implemented by two charged swaps and the existing first-component map. -/
theorem mapSecond_isPolyTime {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    (F : β → γ) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (fun p : α × β => (p.1,F p.2)) := by
  let s₁ : α × β → β × α := swap
  let m : β × α → γ × α := Shared.ComplexityBridge.TM2TypedPairMap.pairMap F
  let s₂ : γ × α → α × γ := swap
  have h₁ : ComplexityTheory.IsPolyTime s₁ := swap_isPolyTime
  have h₂ : ComplexityTheory.IsPolyTime m := Shared.ComplexityBridge.TM2TypedPairMap.pairMap_isPolyTime F hF
  have h₃ : ComplexityTheory.IsPolyTime s₂ := swap_isPolyTime
  have h₁₂ := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp s₁ m h₁ h₂
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp (fun p => m (s₁ p)) s₂ h₁₂ h₃
  simpa [s₁,s₂,m,swap,Shared.ComplexityBridge.TM2TypedPairMap.pairMap] using h

/-- The actual guarded-clause constructor, with the index and clause both
encoded as a canonical pair, is polynomial time. -/
theorem guardClause_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × Shared.ComplexityBridge.CNF.Clause =>
      Shared.ComplexityBridge.CNFDisjunction.guardClause p.1 p.2) := by
  let F : Nat × Shared.ComplexityBridge.CNF.Clause → Nat × Shared.ComplexityBridge.CNF.Clause :=
    fun p => (p.1,Shared.ComplexityBridge.CNFDisjunction.evenClause p.2)
  have hf : ComplexityTheory.IsPolyTime F := mapSecond_isPolyTime _ Shared.ComplexityBridge.CNFEvenClause.evenClause_isPolyTime
  have hg := Shared.ComplexityBridge.TM2TypedPairMap.prependGuard_isPolyTime
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp F
    Shared.ComplexityBridge.TM2TypedPairMap.prependGuard hf hg
  simpa [F,Shared.ComplexityBridge.TM2TypedPairMap.prependGuard,
    Shared.ComplexityBridge.CNFDisjunction.guardClause] using h

namespace Fixtures
example : ∃ t ≤ 7, runSteps machine.step t (Turing.initList machine [false]) =
    some (Turing.haltList machine [false]) := by
  simpa [BitstringEncoding.delimit] using run_bits [] []
example : ∃ t ≤ 14, runSteps machine.step t (Turing.initList machine [true,true,false,false]) =
    some (Turing.haltList machine [true,false,false,true]) := by
  simpa [BitstringEncoding.delimit] using run_bits [true] [false]
end Fixtures

end Shared.ComplexityBridge.TM2PairSwap
