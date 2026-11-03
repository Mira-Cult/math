import Shared.ComplexityBridge.CNFBinaryPairAdd

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Append two canonically encoded lists using a finite TM2. The machine
first undelimits the first list encoding and preserves the second suffix,
then transfers both to the output in order. -/
namespace Shared.ComplexityBridge.TM2ListAppend
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNFBinaryPairAdd

/-- `readLeft` scans the suffix, `readRight` scans the prefix. The Boolean
state distinguishes which restored stack should be followed by another scan. -/
def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .done => .load (fun _ => .inr (true,none,none)) (.goto (fun _ => .inr .readLeft))
  | .inl l => liftU (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr .readLeft => .pop .right (fun _ h => .inr (true,h,none))
      (.branch (fun v => (aState v).2.1.isSome)
        (.push .scratch (fun v => (aState v).2.1.getD false) (.goto (fun _ => .inr .readLeft)))
        (.goto (fun _ => .inr .restore)))
  | .inr .readRight => .pop .left (fun _ h => .inr (false,h,none))
      (.branch (fun v => (aState v).2.1.isSome)
        (.push .scratch (fun v => (aState v).2.1.getD false) (.goto (fun _ => .inr .readRight)))
        (.goto (fun _ => .inr .restore)))
  | .inr .restore => .pop .scratch (fun v h => .inr ((aState v).1,h,none))
      (.branch (fun v => (aState v).2.1.isSome)
        (.push .output (fun v => (aState v).2.1.getD false) (.goto (fun _ => .inr .restore)))
        (.branch (fun v => (aState v).1)
          (.goto (fun _ => .inr .readRight)) (.load (fun _ => .inl none) .halt)))

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
theorem stable (q : U.Cfg) (h : terminal q) : U.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.done at h
    subst l
    rfl

theorem loader_step (q : U.Cfg) (h : ¬ terminal q) :
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

def cfg (l : AL) (flag : Bool) (v : Option Bool) (a b scratch output : List Bool) : machine.Cfg :=
  ⟨some (.inr l),.inr (flag,v,none),Shared.ComplexityBridge.CNFBinaryAdd.stackVals a b scratch output⟩

theorem dispatch (a b : List Bool) :
    machine.step (uEmbed [] (Shared.ComplexityBridge.TM2Undelimit.cfg .done none b [] a)) =
      some (cfg .readLeft true none a b [] []) := by
  change some (Cfg.mk _ _ _) = _
  congr 2

theorem right_cons (v : Option Bool) (x : Bool) (a b scratch output : List Bool) :
    machine.step (cfg .readLeft true v a (x::b) scratch output) =
      some (cfg .readLeft true (some x) a b (x::scratch) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem right_nil (v : Option Bool) (a scratch output : List Bool) :
    machine.step (cfg .readLeft true v a [] scratch output) = some (cfg .restore true none a [] scratch output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem left_cons (v : Option Bool) (x : Bool) (a scratch output : List Bool) :
    machine.step (cfg .readRight false v (x::a) [] scratch output) =
      some (cfg .readRight false (some x) a [] (x::scratch) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem left_nil (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .readRight false v [] [] scratch output) = some (cfg .restore false none [] [] scratch output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem restore_cons (flag : Bool) (v : Option Bool) (x : Bool) (a scratch output : List Bool) :
    machine.step (cfg .restore flag v a [] (x::scratch) output) =
      some (cfg .restore flag (some x) a [] scratch (x::output)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem restore_right_nil (v : Option Bool) (a output : List Bool) :
    machine.step (cfg .restore true v a [] [] output) = some (cfg .readRight true none a [] [] output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,aState]

theorem restore_left_nil (v : Option Bool) (output : List Bool) :
    machine.step (cfg .restore false v [] [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryAdd.stackVals,Function.update,Turing.haltList,machine]

/-- Both scan labels reset the flag before examining a symbol, so either flag
can enter the left scan. -/
theorem left_cons_any (flag : Bool) (v : Option Bool) (x : Bool) (a scratch output : List Bool) :
    machine.step (cfg .readRight flag v (x::a) [] scratch output) =
      some (cfg .readRight false (some x) a [] (x::scratch) output) := by
  cases flag <;> exact left_cons v x a scratch output

theorem left_nil_any (flag : Bool) (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .readRight flag v [] [] scratch output) = some (cfg .restore false none [] [] scratch output) := by
  cases flag <;> exact left_nil v scratch output

theorem right_run (b a scratch output : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step b.length (cfg .readLeft true v a b scratch output) =
      some (cfg .readLeft true v' a [] (b.reverse++scratch) output) := by
  induction b generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons x b ih =>
    obtain ⟨v',hr⟩ := ih (x::scratch) (some x)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,right_cons]
    simpa [List.reverse_cons,List.append_assoc] using hr

theorem left_run (a scratch output : List Bool) (flag : Bool) (v : Option Bool) :
    ∃ flag' v', runSteps machine.step a.length (cfg .readRight flag v a [] scratch output) =
      some (cfg .readRight flag' v' [] [] (a.reverse++scratch) output) := by
  induction a generalizing scratch flag v with
  | nil => exact ⟨flag,v,by simp [runSteps]⟩
  | cons x a ih =>
    obtain ⟨flag',v',hr⟩ := ih (x::scratch) false (some x)
    refine ⟨flag',v',?_⟩
    rw [List.length_cons,runSteps_front,left_cons_any]
    simpa [List.reverse_cons,List.append_assoc] using hr

theorem restore_run (scratch a output : List Bool) (flag : Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore flag v a [] scratch output) =
      some (cfg .restore flag v' a [] [] (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons x scratch ih =>
    obtain ⟨v',hr⟩ := ih (x::output) (some x)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using hr

theorem right_phase (a b : List Bool) :
    runSteps machine.step (2*b.length+2) (cfg .readLeft true none a b [] []) =
      some (cfg .readRight true none a [] [] b) := by
  obtain ⟨v,hs⟩ := right_run b a [] [] none
  simp only [List.append_nil] at hs
  obtain ⟨w,hr⟩ := restore_run b.reverse a [] true none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  have hcost : 2*b.length+2 = b.length+1+(b.length+1) := by omega
  rw [hcost,runSteps_add,runSteps_add,hs]
  change runSteps machine.step 1 (cfg .readLeft true v a [] b.reverse []) >>= _ = _
  rw [show runSteps machine.step 1 (cfg .readLeft true v a [] b.reverse []) =
    machine.step (cfg .readLeft true v a [] b.reverse []) by rfl,right_nil]
  change runSteps machine.step (b.length+1) (cfg .restore true none a [] b.reverse []) = _
  rw [runSteps_add,hr]
  exact restore_right_nil w a b

theorem left_phase (a b : List Bool) :
    runSteps machine.step (2*a.length+2) (cfg .readRight true none a [] [] b) =
      some (Turing.haltList machine (a++b)) := by
  obtain ⟨flag,v,hs⟩ := left_run a [] b true none
  simp only [List.append_nil] at hs
  obtain ⟨w,hr⟩ := restore_run a.reverse [] b false none
  simp only [List.reverse_reverse,List.length_reverse] at hr
  have hcost : 2*a.length+2 = a.length+1+(a.length+1) := by omega
  rw [hcost,runSteps_add,runSteps_add,hs]
  change runSteps machine.step 1 (cfg .readRight flag v [] [] a.reverse b) >>= _ = _
  rw [show runSteps machine.step 1 (cfg .readRight flag v [] [] a.reverse b) =
    machine.step (cfg .readRight flag v [] [] a.reverse b) by rfl,left_nil_any]
  change runSteps machine.step (a.length+1) (cfg .restore false none [] [] a.reverse b) = _
  rw [runSteps_add,hr]
  exact restore_left_nil w (a++b)

/-- The serialized pair's delimiter is removed and its two raw payloads
are concatenated. The entire valid-input run has an explicit linear bound. -/
theorem run_bits (a b : List Bool) :
    ∃ t ≤ 5*a.length+2*b.length+7,
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.delimit a ++ b)) =
        some (Turing.haltList machine (a++b)) := by
  let fin := Shared.ComplexityBridge.TM2Undelimit.cfg .done none b [] a
  have hl := Shared.ComplexityBridge.TM2Undelimit.valid_run a b
  change runSteps U.step (3*a.length+2) (Turing.initList U (BitstringEncoding.delimit a ++ b)) = some fin at hl
  obtain ⟨d,hd,he⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    U.step machine.step (uEmbed []) terminal stable loader_step _ _ fin (by rfl) hl
  refine ⟨d+1+(2*b.length+2)+(2*a.length+2),by omega,?_⟩
  rw [initial_eq,show d+1+(2*b.length+2)+(2*a.length+2) =
    d+(1+((2*b.length+2)+(2*a.length+2))) by omega,runSteps_add,he]
  change runSteps machine.step (1+((2*b.length+2)+(2*a.length+2))) (uEmbed [] fin) = _
  rw [Nat.add_comm 1 _,runSteps_front,dispatch]
  change runSteps machine.step ((2*b.length+2)+(2*a.length+2)) (cfg .readLeft true none a b [] []) = _
  rw [runSteps_add,right_phase]
  exact left_phase a b

theorem list_encoding_append {α : Type} [BitstringEncoding α] (xs ys : List α) :
    BitstringEncoding.bitEncode (xs++ys) = BitstringEncoding.bitEncode xs ++ BitstringEncoding.bitEncode ys := by
  change (((xs++ys).map BitstringEncoding.bitEncode).map BitstringEncoding.delimit).flatten = _
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change BitstringEncoding.bitEncode (xs++ys) = BitstringEncoding.bitEncode xs ++ BitstringEncoding.bitEncode ys at ih
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++
      BitstringEncoding.bitEncode (xs++ys) =
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode xs) ++
        BitstringEncoding.bitEncode ys
    rw [ih,List.append_assoc]

def append {α : Type} (p : List α × List α) : List α := p.1++p.2

/-- List concatenation is polynomial time for any pinned element encoding;
its proof charges parsing, both transfers, and the full pair input length. -/
noncomputable def timeMachine {α : Type} [BitstringEncoding α] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : List α × List α → List Bool)
      (BitstringEncoding.bitEncode : List α → List Bool) (append (α := α)) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 4
  outputsFun p := by
    classical
    rcases p with ⟨xs,ys⟩
    let a := BitstringEncoding.bitEncode xs
    let b := BitstringEncoding.bitEncode ys
    have hi : BitstringEncoding.bitEncode (xs,ys) = BitstringEncoding.delimit a ++ b := by rfl
    have ho : BitstringEncoding.bitEncode (append (xs,ys)) = a++b := list_encoding_append xs ys
    let t := Nat.find (run_bits a b)
    have ht := (Nat.find_spec (run_bits a b)).1
    have hr := (Nat.find_spec (run_bits a b)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode (xs,ys)).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (append (xs,ys))).map id))
      simpa [hi,ho] using hr
    · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,hi,
        List.length_append,BitstringEncoding.length_delimit]
      omega

theorem append_isPolyTime {α : Type} [BitstringEncoding α] : ComplexityTheory.IsPolyTime (append (α := α)) := ⟨timeMachine⟩

def cons {α : Type} (p : α × List α) : List α := p.1::p.2

theorem cons_encoding {α : Type} [BitstringEncoding α] (p : α × List α) :
    BitstringEncoding.bitEncode (cons p) = BitstringEncoding.bitEncode p := by
  rcases p with ⟨x,xs⟩
  rfl

/-- The pinned list and pair encodings coincide for cons, so the finite
identity machine implements the operation, including its output boundary. -/
noncomputable def consTimeMachine {α : Type} [BitstringEncoding α] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : α × List α → List Bool)
      (BitstringEncoding.bitEncode : List α → List Bool) (cons (α := α)) where
  toTM2ComputableAux := (Turing.idComputableInPolyTime (BitstringEncoding.bitEncode : α × List α → List Bool)).toTM2ComputableAux
  time := (Turing.idComputableInPolyTime (BitstringEncoding.bitEncode : α × List α → List Bool)).time
  outputsFun p := by
    have h := (Turing.idComputableInPolyTime (BitstringEncoding.bitEncode : α × List α → List Bool)).outputsFun p
    simpa only [cons_encoding,id_eq] using h

theorem cons_isPolyTime {α : Type} [BitstringEncoding α] : ComplexityTheory.IsPolyTime (cons (α := α)) := ⟨consTimeMachine⟩

/-- The same finite machines apply to both levels of the CNF syntax. -/
theorem clause_append_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Shared.ComplexityBridge.CNF.Clause × Shared.ComplexityBridge.CNF.Clause => p.1++p.2) :=
  append_isPolyTime

theorem formula_append_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Shared.ComplexityBridge.CNF.Formula × Shared.ComplexityBridge.CNF.Formula => p.1++p.2) :=
  append_isPolyTime

theorem literal_cons_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Shared.ComplexityBridge.CNF.Literal × Shared.ComplexityBridge.CNF.Clause => p.1::p.2) :=
  cons_isPolyTime

namespace Fixtures
example : ∃ t ≤ 7, runSteps machine.step t (Turing.initList machine [false]) =
    some (Turing.haltList machine []) := by
  simpa [BitstringEncoding.delimit] using run_bits [] []
example : ∃ t ≤ 14, runSteps machine.step t
    (Turing.initList machine [true,true,false,false]) = some (Turing.haltList machine [true,false]) := by
  simpa [BitstringEncoding.delimit] using run_bits [true] [false]
end Fixtures

end Shared.ComplexityBridge.TM2ListAppend
