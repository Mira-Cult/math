import Shared.ComplexityBridge.RawCNFLookup
import Shared.ComplexityBridge.TM2GenericStackBound

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2WitnessLookup
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Parse := Shared.ComplexityBridge.TM2Undelimit.machine
abbrev Compare := Shared.ComplexityBridge.TM2NumeralCompare.machine
abbrev PKey := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev PLabel := Shared.ComplexityBridge.TM2Undelimit.Label
abbrev CKey := Shared.ComplexityBridge.TM2NumeralCompare.Stack
abbrev CLabel := Shared.ComplexityBridge.TM2NumeralCompare.Label
abbrev CState := Shared.ComplexityBridge.TM2NumeralCompare.State
inductive Key where | vars | witness | query | scratch | left | right deriving DecidableEq
inductive Phase where | start | copy | restore | clearLeft | clearRight | yes | no deriving DecidableEq
instance : Fintype Key := Fintype.ofList [.vars,.witness,.query,.scratch,.left,.right] (by intro k; cases k <;> simp)
instance : Fintype Phase := Fintype.ofList [.start,.copy,.restore,.clearLeft,.clearRight,.yes,.no] (by intro p; cases p <;> simp)
abbrev Label := Phase ⊕ (PLabel ⊕ CLabel)
abbrev State := Bool × Bool × (Option Bool ⊕ (CState ⊕ Option Bool))
def parseVar : State → Option Bool | (_,_,.inl v) => v | _ => none
def cmpVar : State → CState | (_,_,.inr (.inl v)) => v | _ => (none,none,none)
def flagVar : State → Option Bool | (_,_,.inr (.inr v)) => v | _ => none

def pkey : PKey → Key | .input => .vars | .scratch => .scratch | .payload => .left
def ckey : CKey → Key | .left => .left | .right => .right
def pstacks (S : PKey → List Bool) (other : Key → List Bool) : Key → List Bool
  | .vars => S .input | .scratch => S .scratch | .left => S .payload | k => other k
def cstacks (S : CKey → List Bool) (other : Key → List Bool) : Key → List Bool
  | .left => S .left | .right => S .right | k => other k
@[simp] theorem pstacks_apply (S : PKey → List Bool) (other : Key → List Bool) (j : PKey) :
    pstacks S other (pkey j) = S j := by cases j <;> rfl
@[simp] theorem cstacks_apply (S : CKey → List Bool) (other : Key → List Bool) (j : CKey) :
    cstacks S other (ckey j) = S j := by cases j <;> rfl

theorem pupdate (S : PKey → List Bool) (other : Key → List Bool) (j : PKey) (xs : List Bool) :
    pstacks (Function.update S j xs) other = Function.update (pstacks S other) (pkey j) xs := by
  funext k; cases j <;> cases k <;> simp [pstacks,pkey,Function.update]
theorem cupdate (S : CKey → List Bool) (other : Key → List Bool) (j : CKey) (xs : List Bool) :
    cstacks (Function.update S j xs) other = Function.update (cstacks S other) (ckey j) xs := by
  funext k; cases j <;> cases k <;> simp [cstacks,ckey,Function.update]

def pemb (bit matched : Bool) (other : Key → List Bool) (q : Parse.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),(bit,matched,.inl q.var),pstacks q.stk other⟩
def cemb (bit matched : Bool) (other : Key → List Bool) (q : Compare.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inr l)),(bit,matched,.inr (.inl q.var)),cstacks q.stk other⟩

def liftParse : Stmt (fun _ : PKey => Bool) PLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (pkey j) (fun v => f (parseVar v)) (liftParse q)
  | .peek j f q => .peek (pkey j) (fun v h => (v.1,v.2.1,.inl (f (parseVar v) h))) (liftParse q)
  | .pop j f q => .pop (pkey j) (fun v h => (v.1,v.2.1,.inl (f (parseVar v) h))) (liftParse q)
  | .load f q => .load (fun v => (v.1,v.2.1,.inl (f (parseVar v)))) (liftParse q)
  | .branch f q r => .branch (fun v => f (parseVar v)) (liftParse q) (liftParse r)
  | .goto f => .goto (fun v => .inr (.inl (f (parseVar v))))
  | .halt => .halt

def liftCompare : Stmt (fun _ : CKey => Bool) CLabel CState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (ckey j) (fun v => f (cmpVar v)) (liftCompare q)
  | .peek j f q => .peek (ckey j) (fun v h => (v.1,v.2.1,.inr (.inl (f (cmpVar v) h)))) (liftCompare q)
  | .pop j f q => .pop (ckey j) (fun v h => (v.1,v.2.1,.inr (.inl (f (cmpVar v) h)))) (liftCompare q)
  | .load f q => .load (fun v => (v.1,v.2.1,.inr (.inl (f (cmpVar v))))) (liftCompare q)
  | .branch f q r => .branch (fun v => f (cmpVar v)) (liftCompare q) (liftCompare r)
  | .goto f => .goto (fun v => .inr (.inr (f (cmpVar v))))
  | .halt => .halt

theorem liftParse_aux (q : Parse.Stmt) (bit matched : Bool) (v : Option Bool) (S : PKey → List Bool) (other : Key → List Bool) :
    stepAux (liftParse q) (bit,matched,.inl v) (pstacks S other) = pemb bit matched other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftParse,stepAux,parseVar,pstacks_apply]
    rw [← pupdate S other j (f v::S j)]; exact ih _ _
  | peek j f q ih =>
    simp only [liftParse,stepAux,parseVar,pstacks_apply]; exact ih _ _
  | pop j f q ih =>
    simp only [liftParse,stepAux,parseVar,pstacks_apply]
    rw [← pupdate S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftParse,stepAux,parseVar,h,ihq,ihr]

theorem liftCompare_aux (q : Compare.Stmt) (bit matched : Bool) (v : CState) (S : CKey → List Bool) (other : Key → List Bool) :
    stepAux (liftCompare q) (bit,matched,.inr (.inl v)) (cstacks S other) = cemb bit matched other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftCompare,stepAux,cmpVar,cstacks_apply]
    rw [← cupdate S other j (f v::S j)]; exact ih _ _
  | peek j f q ih =>
    simp only [liftCompare,stepAux,cmpVar,cstacks_apply]; exact ih _ _
  | pop j f q ih =>
    simp only [liftCompare,stepAux,cmpVar,cstacks_apply]
    rw [← cupdate S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftCompare,stepAux,cmpVar,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .start => .pop .witness (fun v h => (h.getD false,false,.inr (.inr h)))
      (.branch (fun v => (flagVar v).isSome)
        (.peek .vars (fun v h => (v.1,v.2.1,.inr (.inr h)))
          (.branch (fun v => (flagVar v).isSome)
            (.load (fun v => (v.1,false,.inl none)) (.goto (fun _ => .inr (.inl .header))))
            (.goto (fun _ => .inl .no))))
        (.goto (fun _ => .inl .no)))
  | .inl .copy => .pop .query (fun v h => (v.1,v.2.1,.inr (.inr h)))
      (.branch (fun v => (flagVar v).isSome)
        (.push .scratch (fun v => (flagVar v).getD false) (.goto (fun _ => .inl .copy)))
        (.goto (fun _ => .inl .restore)))
  | .inl .restore => .pop .scratch (fun v h => (v.1,v.2.1,.inr (.inr h)))
      (.branch (fun v => (flagVar v).isSome)
        (.push .query (fun v => (flagVar v).getD false)
          (.push .right (fun v => (flagVar v).getD false) (.goto (fun _ => .inl .restore))))
        (.load (fun v => (v.1,v.2.1,.inr (.inl (none,none,none)))) (.goto (fun _ => .inr (.inr .scan)))))
  | .inl .clearLeft => .pop .left (fun v h => (v.1,v.2.1,.inr (.inr h)))
      (.branch (fun v => (flagVar v).isSome) (.goto (fun _ => .inl .clearLeft)) (.goto (fun _ => .inl .clearRight)))
  | .inl .clearRight => .pop .right (fun v h => (v.1,v.2.1,.inr (.inr h)))
      (.branch (fun v => (flagVar v).isSome) (.goto (fun _ => .inl .clearRight))
        (.branch (fun v => v.2.1) (.branch (fun v => v.1) (.goto (fun _ => .inl .yes)) (.goto (fun _ => .inl .no)))
          (.goto (fun _ => .inl .start))))
  | .inl .yes => .goto (fun _ => .inl .yes)
  | .inl .no => .goto (fun _ => .inl .no)
  | .inr (.inl .done) => .load (fun v => (v.1,false,.inr (.inr none))) (.goto (fun _ => .inl .copy))
  | .inr (.inl .reject) => .goto (fun _ => .inl .no)
  | .inr (.inl l) => liftParse (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr (.inr .accept) => .load (fun v => (v.1,true,.inr (.inr none))) (.goto (fun _ => .inl .clearLeft))
  | .inr (.inr .reject) => .load (fun v => (v.1,false,.inr (.inr none))) (.goto (fun _ => .inl .clearLeft))
  | .inr (.inr l) => liftCompare (Shared.ComplexityBridge.TM2NumeralCompare.program l)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .vars
  k₁ := .left
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .start
  σ := State
  initialState := (false,false,.inr (.inr none))
  m := program

def pTerminal (q : Parse.Cfg) : Prop := q.l = some .done ∨ q.l = some .reject
noncomputable instance : DecidablePred pTerminal := fun _ => Classical.propDecidable _
theorem pStable (q : Parse.Cfg) (h : pTerminal q) : Parse.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.done ∨ l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    rcases h with h | h <;> subst l <;> rfl

theorem pStep (bit matched : Bool) (other : Key → List Bool) (q : Parse.Cfg) (h : ¬ pTerminal q) :
    machine.step (pemb bit matched other q) = (Parse.step q).map (pemb bit matched other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | done => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | header | data | restore =>
        change some (stepAux (liftParse (Shared.ComplexityBridge.TM2Undelimit.program _)) (bit,matched,.inl v) (pstacks S other)) = _
        rw [liftParse_aux]; rfl

def cTerminal (q : Compare.Cfg) : Prop := q.l = some .accept ∨ q.l = some .reject
noncomputable instance : DecidablePred cTerminal := fun _ => Classical.propDecidable _
theorem cStable (q : Compare.Cfg) (h : cTerminal q) : Compare.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2NumeralCompare.Label.accept ∨ l = some Shared.ComplexityBridge.TM2NumeralCompare.Label.reject at h
    rcases h with h | h <;> subst l <;> rfl

theorem cStep (bit matched : Bool) (other : Key → List Bool) (q : Compare.Cfg) (h : ¬ cTerminal q) :
    machine.step (cemb bit matched other q) = (Compare.step q).map (cemb bit matched other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | accept => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | scan | checkLeft | checkRight =>
        change some (stepAux (liftCompare (Shared.ComplexityBridge.TM2NumeralCompare.program _)) (bit,matched,.inr (.inl v)) (cstacks S other)) = _
        rw [liftCompare_aux]; rfl

def stackVals (vars witness query scratch left right : List Bool) : Key → List Bool
  | .vars => vars | .witness => witness | .query => query | .scratch => scratch | .left => left | .right => right

def cfg (l : Phase) (bit matched : Bool) (flag : Option Bool) (vars witness query scratch left right : List Bool) : machine.Cfg :=
  ⟨some (.inl l),(bit,matched,.inr (.inr flag)),stackVals vars witness query scratch left right⟩

theorem start_empty_witness (vars query : List Bool) (bit matched : Bool) (flag : Option Bool) :
    machine.step (cfg .start bit matched flag vars [] query [] [] []) =
      some (cfg .no false false none vars [] query [] [] []) := by
  change some (Cfg.mk _ _ (Function.update (stackVals vars [] query [] [] []) .witness [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem start_empty_vars (b bit matched : Bool) (flag : Option Bool) (witness query : List Bool) :
    machine.step (cfg .start bit matched flag [] (b::witness) query [] [] []) =
      some (cfg .no b false none [] witness query [] [] []) := by
  change some (Cfg.mk _ _ (Function.update (stackVals [] (b::witness) query [] [] []) .witness witness)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem start_cons (v b bit matched : Bool) (flag : Option Bool) (vars witness query : List Bool) :
    machine.step (cfg .start bit matched flag (v::vars) (b::witness) query [] [] []) =
      some (pemb b false (stackVals [] witness query [] [] []) (Turing.initList Parse (v::vars))) := by
  change some (Cfg.mk _ _ (Function.update (stackVals (v::vars) (b::witness) query [] [] []) .witness witness)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,pemb,pstacks,Turing.initList,Function.update,Parse,Shared.ComplexityBridge.TM2Undelimit.machine] <;> rfl

theorem parse_done (bit : Bool) (vars witness query left : List Bool) :
    machine.step (pemb bit false (stackVals [] witness query [] [] [])
      (Shared.ComplexityBridge.TM2Undelimit.cfg .done none vars [] left)) =
      some (cfg .copy bit false none vars witness query [] left []) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> rfl

theorem copy_cons (a bit matched : Bool) (flag : Option Bool) (vars witness query scratch left right : List Bool) :
    machine.step (cfg .copy bit matched flag vars witness (a::query) scratch left right) =
      some (cfg .copy bit matched (some a) vars witness query (a::scratch) left right) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (stackVals vars witness (a::query) scratch left right) .query query) .scratch (a::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem copy_nil (bit matched : Bool) (flag : Option Bool) (vars witness scratch left right : List Bool) :
    machine.step (cfg .copy bit matched flag vars witness [] scratch left right) =
      some (cfg .restore bit matched none vars witness [] scratch left right) := by
  change some (Cfg.mk _ _ (Function.update (stackVals vars witness [] scratch left right) .query [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (a bit matched : Bool) (flag : Option Bool) (vars witness query scratch left right : List Bool) :
    machine.step (cfg .restore bit matched flag vars witness query (a::scratch) left right) =
      some (cfg .restore bit matched (some a) vars witness (a::query) scratch left (a::right)) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (Function.update (stackVals vars witness query (a::scratch) left right) .scratch scratch) .query (a::query)) .right (a::right))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (bit matched : Bool) (flag : Option Bool) (vars witness query left right : List Bool) :
    machine.step (cfg .restore bit matched flag vars witness query [] left right) =
      some (cemb bit matched (stackVals vars witness query [] [] []) (Shared.ComplexityBridge.TM2NumeralCompare.cfg .scan (none,none,none) left right)) := by
  change some (Cfg.mk _ _ (Function.update (stackVals vars witness query [] left right) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,cemb,cstacks,Shared.ComplexityBridge.TM2NumeralCompare.cfg,Shared.ComplexityBridge.TM2NumeralCompare.stackVals,Function.update]

theorem copy_loop (query vars witness scratch left right : List Bool) (bit matched : Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step query.length (cfg .copy bit matched flag vars witness query scratch left right) =
      some (cfg .copy bit matched flag' vars witness [] (query.reverse++scratch) left right) := by
  induction query generalizing scratch flag with
  | nil => exact ⟨flag, by simp [runSteps]⟩
  | cons b query ih =>
    obtain ⟨flag',h⟩ := ih (b::scratch) (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,copy_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore_loop (scratch vars witness query left right : List Bool) (bit matched : Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step scratch.length (cfg .restore bit matched flag vars witness query scratch left right) =
      some (cfg .restore bit matched flag' vars witness (scratch.reverse++query) [] left (scratch.reverse++right)) := by
  induction scratch generalizing query right flag with
  | nil => exact ⟨flag, by simp [runSteps]⟩
  | cons b scratch ih =>
    obtain ⟨flag',h⟩ := ih (b::query) (b::right) (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem copy_run (query vars witness left : List Bool) (bit : Bool) :
    runSteps machine.step (2*query.length+2) (cfg .copy bit false none vars witness query [] left []) =
      some (cemb bit false (stackVals vars witness query [] [] []) (Shared.ComplexityBridge.TM2NumeralCompare.cfg .scan (none,none,none) left query)) := by
  obtain ⟨v,hc⟩ := copy_loop query vars witness [] left [] bit false none
  simp only [List.append_nil] at hc
  obtain ⟨w,hr⟩ := restore_loop query.reverse vars witness [] left [] bit false none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  have hn : 2*query.length+2 = query.length+(1+(query.length+1)) := by omega
  rw [hn,runSteps_add,hc]
  change runSteps machine.step (1+(query.length+1)) (cfg .copy bit false v vars witness [] query.reverse left []) = _
  rw [runSteps_add]
  change (machine.step (cfg .copy bit false v vars witness [] query.reverse left [])).bind (runSteps machine.step (query.length+1)) = _
  rw [copy_nil]
  change runSteps machine.step (query.length+1) (cfg .restore bit false none vars witness [] query.reverse left []) = _
  rw [runSteps_add,hr]
  exact restore_nil bit false w vars witness query left query

theorem compare_done (q : Compare.Cfg) (bit result : Bool) (vars witness query : List Bool)
    (h : q.l = some (if result then .accept else .reject)) :
    machine.step (cemb bit false (stackVals vars witness query [] [] []) q) =
      some (cfg .clearLeft bit result none vars witness query [] (q.stk .left) (q.stk .right)) := by
  cases q with
  | mk l v S =>
    cases result <;> simp only [Bool.false_eq_true,if_false,if_true] at h <;> subst l <;>
      change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _) <;> congr 2 <;> funext k <;> cases k <;> rfl

theorem clearLeft_cons (a bit result : Bool) (flag : Option Bool) (vars witness query left right : List Bool) :
    machine.step (cfg .clearLeft bit result flag vars witness query [] (a::left) right) =
      some (cfg .clearLeft bit result (some a) vars witness query [] left right) := by
  change some (Cfg.mk _ _ (Function.update (stackVals vars witness query [] (a::left) right) .left left)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem clearLeft_nil (bit result : Bool) (flag : Option Bool) (vars witness query right : List Bool) :
    machine.step (cfg .clearLeft bit result flag vars witness query [] [] right) =
      some (cfg .clearRight bit result none vars witness query [] [] right) := by
  change some (Cfg.mk _ _ (Function.update (stackVals vars witness query [] [] right) .left [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem clearRight_cons (a bit result : Bool) (flag : Option Bool) (vars witness query right : List Bool) :
    machine.step (cfg .clearRight bit result flag vars witness query [] [] (a::right)) =
      some (cfg .clearRight bit result (some a) vars witness query [] [] right) := by
  change some (Cfg.mk _ _ (Function.update (stackVals vars witness query [] [] (a::right)) .right right)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem clearRight_nil (bit result : Bool) (flag : Option Bool) (vars witness query : List Bool) :
    machine.step (cfg .clearRight bit result flag vars witness query [] [] []) =
      some (cfg (if result then (if bit then .yes else .no) else .start) bit result none vars witness query [] [] []) := by
  cases bit <;> cases result <;>
    change some (Cfg.mk _ _ (Function.update (stackVals vars witness query [] [] []) .right [])) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

theorem clearLeft_loop (left right vars witness query : List Bool) (bit result : Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step left.length (cfg .clearLeft bit result flag vars witness query [] left right) =
      some (cfg .clearLeft bit result flag' vars witness query [] [] right) := by
  induction left generalizing flag with
  | nil => exact ⟨flag,rfl⟩
  | cons a left ih =>
    obtain ⟨flag',h⟩ := ih (some a)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,clearLeft_cons]; exact h

theorem clearRight_loop (right vars witness query : List Bool) (bit result : Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step right.length (cfg .clearRight bit result flag vars witness query [] [] right) =
      some (cfg .clearRight bit result flag' vars witness query [] [] []) := by
  induction right generalizing flag with
  | nil => exact ⟨flag,rfl⟩
  | cons a right ih =>
    obtain ⟨flag',h⟩ := ih (some a)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,clearRight_cons]; exact h

theorem clear_run (left right vars witness query : List Bool) (bit result : Bool) :
    runSteps machine.step (left.length+right.length+2) (cfg .clearLeft bit result none vars witness query [] left right) =
      some (cfg (if result then (if bit then .yes else .no) else .start) bit result none vars witness query [] [] []) := by
  obtain ⟨v,hl⟩ := clearLeft_loop left right vars witness query bit result none
  obtain ⟨w,hr⟩ := clearRight_loop right vars witness query bit result none
  have hn : left.length+right.length+2 = left.length+(1+(right.length+1)) := by omega
  rw [hn,runSteps_add,hl]
  change runSteps machine.step (1+(right.length+1)) (cfg .clearLeft bit result v vars witness query [] [] right) = _
  rw [runSteps_add]
  change (machine.step (cfg .clearLeft bit result v vars witness query [] [] right)).bind (runSteps machine.step (right.length+1)) = _
  rw [clearLeft_nil]
  change runSteps machine.step (right.length+1) (cfg .clearRight bit result none vars witness query [] [] right) = _
  rw [runSteps_add,hr]
  exact clearRight_nil bit result w vars witness query

def frames (vars : List (List Bool)) : List Bool := vars.flatMap BitstringEncoding.delimit

theorem frames_cons (v : List Bool) (vs : List (List Bool)) :
    frames (v::vs) = BitstringEncoding.delimit v ++ frames vs := by simp [frames]

theorem frames_length_bound (v : List Bool) (vs : List (List Bool)) :
    v.length + (frames vs).length + 1 ≤ (frames (v::vs)).length := by
  rw [frames_cons,List.length_append,BitstringEncoding.length_delimit]; omega

theorem frames_count_bound (vars : List (List Bool)) : vars.length ≤ (frames vars).length := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    have hh := frames_length_bound v vs
    simp only [List.length_cons]
    omega

theorem start_nonempty (v : List Bool) (vs : List (List Bool)) (b bit matched : Bool) (flag : Option Bool) (witness query : List Bool) :
    machine.step (cfg .start bit matched flag (frames (v::vs)) (b::witness) query [] [] []) =
      some (pemb b false (stackVals [] witness query [] [] []) (Turing.initList Parse (frames (v::vs)))) := by
  cases hv : frames (v::vs) with
  | nil =>
    have hh := frames_length_bound v vs
    rw [hv] at hh
    simp at hh
  | cons a rest =>
    exact start_cons a b bit matched flag rest witness query

/-- One full, charged comparison iteration, from an occurrence and witness bit
to either its answer or the next clean loop configuration. -/
theorem iteration (v : List Bool) (vs : List (List Bool)) (b bit matched : Bool) (flag : Option Bool)
    (witness query : List Bool) :
    ∃ t ≤ 8*(v.length+query.length+2) + 2*((v.length+query.length+2)*Shared.ComplexityBridge.TM2GenericStackBound.tableBound Compare),
      runSteps machine.step t (cfg .start bit matched flag (frames (v::vs)) (b::witness) query [] [] []) =
        some (cfg (if Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v) then (if b then .yes else .no) else .start)
          b (Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v)) none (frames vs) witness query [] [] []) := by
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Compare
  let otherP := stackVals [] witness query [] [] []
  let otherC := stackVals (frames vs) witness query [] [] []
  let sourceStart := Turing.initList Parse (frames (v::vs))
  let sourceEnd := Shared.ComplexityBridge.TM2Undelimit.cfg .done none (frames vs) [] v
  have hparse := Shared.ComplexityBridge.TM2Undelimit.valid_run v (frames vs)
  rw [← frames_cons] at hparse
  change runSteps Parse.step (3*v.length+2) sourceStart = some sourceEnd at hparse
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Parse.step machine.step (pemb b false otherP) pTerminal pStable (pStep b false otherP)
    (3*v.length+2) sourceStart sourceEnd (Or.inl rfl) hparse
  let cmpStart := Shared.ComplexityBridge.TM2NumeralCompare.cfg .scan (none,none,none) v query
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2NumeralCompare.compare_progress v query
  change runSteps Compare.step n cmpStart = some q at hr
  have hterm : cTerminal q := by
    unfold cTerminal
    by_cases he : Computability.decodeNat v = Computability.decodeNat query
    · left; simpa [he] using hq
    · right; simpa [he] using hq
  obtain ⟨c,hc,hcr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Compare.step machine.step (cemb b false otherC) cTerminal cStable (cStep b false otherC)
    n cmpStart q hterm hr
  let result := Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v)
  have hresult : q.l = some (if result then .accept else .reject) := by
    by_cases he : Computability.decodeNat query = Computability.decodeNat v
    · have hz : result = true := (Shared.ComplexityBridge.TM2NumeralPairCompare.answer_correct query v).2 he
      simp [hz,he.symm] at hq ⊢
      exact hq
    · have hz : result = false := by
        cases hv : result with
        | false => rfl
        | true => exact False.elim (he ((Shared.ComplexityBridge.TM2NumeralPairCompare.answer_correct query v).1 hv))
      have he' : Computability.decodeNat v ≠ Computability.decodeNat query := Ne.symm he
      simp [hz,he'] at hq ⊢
      exact hq
  have hn' : n ≤ v.length+query.length+2 := by have hh := max_le (Nat.le_add_right v.length query.length) (Nat.le_add_left query.length v.length); omega
  have hmul : n*D ≤ (v.length+query.length+2)*D := Nat.mul_le_mul_right D hn'
  have hleft := Shared.ComplexityBridge.TM2GenericStackBound.run_length Compare n cmpStart q hr .left
  have hright := Shared.ComplexityBridge.TM2GenericStackBound.run_length Compare n cmpStart q hr .right
  change (q.stk .left).length ≤ v.length+n*D at hleft
  change (q.stk .right).length ≤ query.length+n*D at hright
  have hclean : (q.stk .left).length+(q.stk .right).length ≤ v.length+query.length+2*((v.length+query.length+2)*D) := by omega
  let d := (q.stk .left).length+(q.stk .right).length+2
  have hdr := clear_run (q.stk .left) (q.stk .right) (frames vs) witness query b result
  refine ⟨1+a+1+(2*query.length+2)+c+1+d,?_,?_⟩
  · change 1+a+1+(2*query.length+2)+c+1+d ≤ 8*(v.length+query.length+2)+2*((v.length+query.length+2)*D)
    dsimp [d]; omega
  · have htotal : 1+a+1+(2*query.length+2)+c+1+d = 1+(a+(1+((2*query.length+2)+(c+(1+d))))) := by omega
    rw [htotal,runSteps_add]
    change (machine.step (cfg .start bit matched flag (frames (v::vs)) (b::witness) query [] [] [])).bind _ = _
    rw [start_nonempty]
    change runSteps machine.step (a+(1+((2*query.length+2)+(c+(1+d))))) (pemb b false otherP sourceStart) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+((2*query.length+2)+(c+(1+d)))) (pemb b false otherP sourceEnd) = _
    rw [runSteps_add]
    change (machine.step (pemb b false otherP sourceEnd)).bind _ = _
    rw [parse_done]
    change runSteps machine.step ((2*query.length+2)+(c+(1+d))) (cfg .copy b false none (frames vs) witness query [] v []) = _
    rw [runSteps_add,copy_run]
    change runSteps machine.step (c+(1+d)) (cemb b false otherC cmpStart) = _
    rw [runSteps_add,hcr]
    change runSteps machine.step (1+d) (cemb b false otherC q) = _
    rw [runSteps_add]
    change (machine.step (cemb b false otherC q)).bind _ = _
    rw [compare_done q b result (frames vs) witness query hresult]
    exact hdr

noncomputable def iterationBound (B : Nat) : Nat :=
  8*(B+2) + 2*((B+2)*Shared.ComplexityBridge.TM2GenericStackBound.tableBound Compare)

theorem iterationBound_pos (B : Nat) : 1 ≤ iterationBound B := by
  unfold iterationBound; omega

theorem iterationBound_mono {A B : Nat} (h : A ≤ B) : iterationBound A ≤ iterationBound B := by
  unfold iterationBound
  have hh := Nat.mul_le_mul_right (Shared.ComplexityBridge.TM2GenericStackBound.tableBound Compare) (show A+2 ≤ B+2 by omega)
  omega

/-- For loaded, well-framed occurrences, each loop performs finitely many
comparison blocks, retains the query and stops at the first matching witness.
The common bound B includes the entire framed list and the query. -/
theorem lookup_progress_bounded (vars : List (List Bool)) (witness query : List Bool)
    (bit matched : Bool) (flag : Option Bool) (B : Nat)
    (hB : (frames vars).length+query.length ≤ B) :
    ∃ t ≤ (vars.length+1)*iterationBound B, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start bit matched flag (frames vars) witness query [] [] []) = some q ∧
      q.l = some (.inl (if Shared.ComplexityBridge.RawCNFLookup.lookup vars witness query then .yes else .no)) := by
  induction vars generalizing witness bit matched flag with
  | nil =>
    cases witness with
    | nil =>
      refine ⟨1,?_,cfg .no false false none [] [] query [] [] [],?_,?_⟩
      · simpa using iterationBound_pos B
      · change machine.step (cfg .start bit matched flag (frames []) [] query [] [] []) = _
        simpa [frames] using start_empty_witness [] query bit matched flag
      · rfl
    | cons b witness =>
      refine ⟨1,?_,cfg .no b false none [] witness query [] [] [],?_,?_⟩
      · simpa using iterationBound_pos B
      · change machine.step (cfg .start bit matched flag (frames []) (b::witness) query [] [] []) = _
        simpa [frames] using start_empty_vars b bit matched flag witness query
      · rfl
  | cons v vs ih =>
    cases witness with
    | nil =>
      refine ⟨1,?_,cfg .no false false none (frames (v::vs)) [] query [] [] [],?_,?_⟩
      · have hp := iterationBound_pos B
        have hmul : iterationBound B ≤ (vs.length+2)*iterationBound B := by
          calc
            iterationBound B = 1*iterationBound B := by simp
            _ ≤ (vs.length+2)*iterationBound B := Nat.mul_le_mul_right _ (by omega)
        simpa [List.length_cons,Nat.add_assoc] using le_trans hp hmul
      · exact start_empty_witness (frames (v::vs)) query bit matched flag
      · rfl
    | cons b witness =>
      have hframe := frames_length_bound v vs
      have hvB : v.length+query.length ≤ B := by omega
      have htailB : (frames vs).length+query.length ≤ B := by omega
      obtain ⟨t,ht,hr⟩ := iteration v vs b bit matched flag witness query
      have htB : t ≤ iterationBound B := le_trans ht (iterationBound_mono hvB)
      cases he : Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v) with
      | true =>
        refine ⟨t,?_,cfg (if b then .yes else .no) b true none (frames vs) witness query [] [] [],?_,?_⟩
        · have hm : iterationBound B ≤ (vs.length+2)*iterationBound B := by
            calc
              iterationBound B = 1*iterationBound B := by simp
              _ ≤ (vs.length+2)*iterationBound B := Nat.mul_le_mul_right _ (by omega)
          simpa [List.length_cons,Nat.add_assoc] using le_trans htB hm
        · simpa [he] using hr
        · cases b <;> simp [Shared.ComplexityBridge.RawCNFLookup.lookup,he,cfg]
      | false =>
        obtain ⟨u,hu,q,hq,hqLabel⟩ := ih witness b false none htailB
        refine ⟨t+u,?_,q,?_,?_⟩
        · simp only [List.length_cons]
          have heq : (vs.length+2)*iterationBound B = (vs.length+1)*iterationBound B + iterationBound B := by
            calc
              (vs.length+2)*iterationBound B = ((vs.length+1)+1)*iterationBound B := by simp [Nat.add_assoc]
              _ = (vs.length+1)*iterationBound B + iterationBound B := by simp [Nat.add_mul]
          rw [heq]
          omega
        · rw [runSteps_add,hr]
          simpa [he] using hq
        · simpa [Shared.ComplexityBridge.RawCNFLookup.lookup,he] using hqLabel

theorem lookup_progress (vars : List (List Bool)) (witness query : List Bool)
    (bit matched : Bool) (flag : Option Bool) :
    ∃ t ≤ ((frames vars).length+query.length+1)*iterationBound ((frames vars).length+query.length), ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start bit matched flag (frames vars) witness query [] [] []) = some q ∧
      q.l = some (.inl (if Shared.ComplexityBridge.RawCNFLookup.lookup vars witness query then .yes else .no)) := by
  obtain ⟨t,ht,q,hr,hq⟩ := lookup_progress_bounded vars witness query bit matched flag _ (Nat.le_refl _)
  refine ⟨t,?_,q,hr,hq⟩
  have hv := frames_count_bound vars
  have hm := Nat.mul_le_mul_right (iterationBound ((frames vars).length+query.length))
    (show vars.length+1 ≤ (frames vars).length+query.length+1 by omega)
  omega

/-- The finite lookup loop implements the verifier's canonical assignment
semantics, including noncanonical representations of the same variable. -/
theorem lookup_progress_assignment (vars : List (List Bool)) (witness query : List Bool)
    (bit matched : Bool) (flag : Option Bool) :
    ∃ t ≤ ((frames vars).length+query.length+1)*iterationBound ((frames vars).length+query.length), ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start bit matched flag (frames vars) witness query [] [] []) = some q ∧
      q.l = some (.inl (if Shared.ComplexityBridge.CNF.assignment (vars.map Computability.decodeNat) witness (Computability.decodeNat query) then .yes else .no)) := by
  simpa [Shared.ComplexityBridge.RawCNFLookup.lookup_correct] using lookup_progress vars witness query bit matched flag

namespace Fixtures
example : (runSteps machine.step 30 (cfg .start false false none (frames [[false]]) [true] [false,true] [] [] [])).map
    (fun q => match q.l with | some (.inl .yes) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inl .yes) => true | _ => false)
    (runSteps machine.step 30 (cfg .start false false none (frames [[false]]) [true] [false,true] [] [] [])) : Option Bool) = _
  decide
example : (runSteps machine.step 35 (cfg .start false false none (frames [[false],[false,true]]) [false,true] [false] [] [] [])).map
    (fun q => match q.l with | some (.inl .no) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inl .no) => true | _ => false)
    (runSteps machine.step 35 (cfg .start false false none (frames [[false],[false,true]]) [false,true] [false] [] [] [])) : Option Bool) = _
  decide
example : (runSteps machine.step 50 (cfg .start false false none (frames [[true],[false]]) [false,true] [false] [] [] [])).map
    (fun q => match q.l with | some (.inl .yes) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inl .yes) => true | _ => false)
    (runSteps machine.step 50 (cfg .start false false none (frames [[true],[false]]) [false,true] [false] [] [] [])) : Option Bool) = _
  decide
example : (runSteps machine.step 1 (cfg .start false false none (frames [[false]]) [] [false] [] [] [])).map
    (fun q => match q.l with | some (.inl .no) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inl .no) => true | _ => false)
    (runSteps machine.step 1 (cfg .start false false none (frames [[false]]) [] [false] [] [] [])) : Option Bool) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2WitnessLookup
