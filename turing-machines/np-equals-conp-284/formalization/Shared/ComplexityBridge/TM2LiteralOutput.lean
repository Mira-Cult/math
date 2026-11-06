import Shared.ComplexityBridge.TM2LiteralParse
import Shared.ComplexityBridge.TM2GenericStackBound
import Shared.ComplexityBridge.TM2TripleRepack

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2LiteralOutput
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2LiteralParse.machine
abbrev SKey := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev SourceLabel := Shared.ComplexityBridge.TM2LiteralParse.Label
abbrev SourceState := Shared.ComplexityBridge.TM2LiteralParse.State
abbrev Key := SKey ⊕ Unit
inductive Phase where | collect | emit | clearInput | clearScratch | clearPayload deriving DecidableEq
instance : Fintype Phase := Fintype.ofList [.collect,.emit,.clearInput,.clearScratch,.clearPayload] (by intro p; cases p <;> simp)
abbrev Label := SourceLabel ⊕ Phase
abbrev State := SourceState ⊕ (Bool × Option Bool)
def sourceState : State → SourceState | .inl v => v | _ => .inl none
def localState : State → Bool × Option Bool | .inr v => v | _ => (false,none)
def signOf : SourceState → Bool | .inr (some b,_) => b | _ => false

def stackVals (S : SKey → List Bool) (result : List Bool) : Key → List Bool
  | .inl k => S k | .inr _ => result
@[simp] theorem stackVals_apply (S : SKey → List Bool) (result : List Bool) (j : SKey) :
    stackVals S result (.inl j) = S j := rfl

theorem stackVals_update (S : SKey → List Bool) (result : List Bool) (j : SKey) (xs : List Bool) :
    stackVals (Function.update S j xs) result = Function.update (stackVals S result) (.inl j) xs := by
  funext k
  cases k with
  | inr u => cases u; simp [stackVals,Function.update]
  | inl k =>
    by_cases h : k = j
    · subst k; simp [stackVals,Function.update]
    · have hh : (Sum.inl k : Key) ≠ .inl j := by simpa using h
      simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]

def embed (q : Source.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map Sum.inl,.inl q.var,stackVals q.stk []⟩

def lift : Stmt (fun _ : SKey => Bool) SourceLabel SourceState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (.inl j) (fun v => f (sourceState v)) (lift q)
  | .peek j f q => .peek (.inl j) (fun v h => .inl (f (sourceState v) h)) (lift q)
  | .pop j f q => .pop (.inl j) (fun v h => .inl (f (sourceState v) h)) (lift q)
  | .load f q => .load (fun v => .inl (f (sourceState v))) (lift q)
  | .branch f q r => .branch (fun v => f (sourceState v)) (lift q) (lift r)
  | .goto f => .goto (fun v => .inl (f (sourceState v)))
  | .halt => .halt

theorem lift_aux (q : Source.Stmt) (v : SourceState) (S : SKey → List Bool) :
    stepAux (lift q) (.inl v) (stackVals S []) = embed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [lift,stepAux,sourceState,stackVals_apply]
    rw [← stackVals_update S [] j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [lift,stepAux,sourceState,stackVals_apply]; exact ih _ _
  | pop j f q ih =>
    simp only [lift,stepAux,sourceState,stackVals_apply]
    rw [← stackVals_update S [] j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,sourceState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl (.inr .accept) => .push (.inr ()) (fun _ => false)
      (.load (fun v => .inr (signOf (sourceState v),none)) (.goto (fun _ => .inr .collect)))
  | .inl (.inr .reject) => .load (fun _ => .inr (false,none)) (.goto (fun _ => .inr .clearInput))
  | .inl l => lift (Shared.ComplexityBridge.TM2LiteralParse.program l)
  | .inr .collect => .pop (.inl .payload) (fun v h => .inr ((localState v).1,h))
      (.branch (fun v => (localState v).2.isSome)
        (.push (.inl .scratch) (fun v => (localState v).2.getD false) (.goto (fun _ => .inr .collect)))
        (.goto (fun _ => .inr .emit)))
  | .inr .emit => .pop (.inl .scratch) (fun v h => .inr ((localState v).1,h))
      (.branch (fun v => (localState v).2.isSome)
        (.push (.inr ()) (fun v => (localState v).2.getD false)
          (.push (.inr ()) (fun _ => true) (.goto (fun _ => .inr .emit))))
        (.push (.inr ()) (fun v => (localState v).1)
          (.push (.inr ()) (fun _ => true) (.load (fun _ => .inl Source.initialState) .halt))))
  | .inr .clearInput => .pop (.inl .input) (fun v h => .inr ((localState v).1,h))
      (.branch (fun v => (localState v).2.isSome) (.goto (fun _ => .inr .clearInput)) (.goto (fun _ => .inr .clearScratch)))
  | .inr .clearScratch => .pop (.inl .scratch) (fun v h => .inr ((localState v).1,h))
      (.branch (fun v => (localState v).2.isSome) (.goto (fun _ => .inr .clearScratch)) (.goto (fun _ => .inr .clearPayload)))
  | .inr .clearPayload => .pop (.inl .payload) (fun v h => .inr ((localState v).1,h))
      (.branch (fun v => (localState v).2.isSome) (.goto (fun _ => .inr .clearPayload))
        (.push (.inr ()) (fun _ => false) (.load (fun _ => .inl Source.initialState) .halt)))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inl .input
  k₁ := .inr ()
  Γ := fun _ => Bool
  Λ := Label
  main := .inl Source.main
  σ := State
  initialState := .inl Source.initialState
  m := program

def terminal (q : Source.Cfg) : Prop := q.l = some (.inr .accept) ∨ q.l = some (.inr .reject)
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inr Shared.ComplexityBridge.TM2LiteralParse.CheckLabel.accept) ∨
      l = some (.inr Shared.ComplexityBridge.TM2LiteralParse.CheckLabel.reject) at h
    rcases h with h | h <;> subst l <;> rfl

theorem source_step (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (embed q) = (Source.step q).map embed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl l =>
        change some (stepAux (lift (Shared.ComplexityBridge.TM2LiteralParse.program (.inl l))) (.inl v) (stackVals S [])) = _
        rw [lift_aux]; rfl
      | inr l => cases l with
        | accept => exact False.elim (h (Or.inl rfl))
        | reject => exact False.elim (h (Or.inr rfl))
        | sign | endSign =>
          change some (stepAux (lift (Shared.ComplexityBridge.TM2LiteralParse.program _)) (.inl v) (stackVals S [])) = _
          rw [lift_aux]; rfl

theorem initial_eq (bits : List Bool) : Turing.initList machine bits = embed (Turing.initList Source bits) := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k
  cases k with
  | inr u => cases u; simp [machine,embed,stackVals,Turing.initList]
  | inl k => cases k <;> simp [machine,embed,stackVals,Turing.initList,Source,Shared.ComplexityBridge.TM2LiteralParse.machine] <;> rfl

def cfg (p : Phase) (sign : Bool) (flag : Option Bool) (input scratch payload result : List Bool) : machine.Cfg :=
  ⟨some (.inr p),.inr (sign,flag),stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals input scratch payload) result⟩

theorem accept_dispatch (name : List Bool) (sign : Bool) :
    machine.step (embed (Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some sign) none [] [] name)) =
      some (cfg .collect sign none [] [] name [false]) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k
  cases k with
  | inr u => cases u; rfl
  | inl k => cases k <;> rfl

def clearRaw (S : SKey → List Bool) : machine.Cfg :=
  ⟨some (.inr .clearInput),.inr (false,none),stackVals S []⟩

theorem reject_dispatch (q : Source.Cfg) (h : q.l = some (.inr .reject)) :
    machine.step (embed q) = some (clearRaw q.stk) := by
  cases q with
  | mk l v S =>
    change l = some (.inr .reject) at h
    subst l
    rfl

theorem collect_cons (sign : Bool) (flag : Option Bool) (b : Bool) (scratch payload result : List Bool) :
    machine.step (cfg .collect sign flag [] scratch (b::payload) result) = some (cfg .collect sign (some b) [] (b::scratch) payload result) := by
  change some (Cfg.mk _ _ (Function.update (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] scratch (b::payload)) result) (.inl .payload) payload)
      (.inl .scratch) (b::scratch))) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem collect_nil (sign : Bool) (flag : Option Bool) (scratch result : List Bool) :
    machine.step (cfg .collect sign flag [] scratch [] result) = some (cfg .emit sign none [] scratch [] result) := by
  change some (Cfg.mk _ _ (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] scratch []) result) (.inl .payload) [])) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem emit_cons (sign : Bool) (flag : Option Bool) (b : Bool) (scratch result : List Bool) :
    machine.step (cfg .emit sign flag [] (b::scratch) [] result) = some (cfg .emit sign (some b) [] scratch [] (true::b::result)) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] (b::scratch) []) result) (.inl .scratch) scratch)
      (.inr ()) (b::result)) (.inr ()) (true::b::result))) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem emit_nil (sign : Bool) (flag : Option Bool) (result : List Bool) :
    machine.step (cfg .emit sign flag [] [] [] result) = some (Turing.haltList machine (true::sign::result)) := by
  change some (Cfg.mk none (Sum.inl Source.initialState : State) (Function.update (Function.update (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] [] []) result) (.inl .scratch) [])
      (.inr ()) (sign::result)) (.inr ()) (true::sign::result))) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update,Turing.haltList,machine]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update,Turing.haltList,machine]

theorem collect_loop (payload scratch result : List Bool) (sign : Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step payload.length (cfg .collect sign flag [] scratch payload result) =
      some (cfg .collect sign flag' [] (payload.reverse++scratch) [] result) := by
  induction payload generalizing scratch flag with
  | nil => exact ⟨flag,by simp [runSteps]⟩
  | cons b payload ih =>
    obtain ⟨flag',h⟩ := ih (b::scratch) (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,collect_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem emit_loop (scratch result : List Bool) (sign : Bool) (flag : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .emit sign flag [] scratch [] result) =
      some (Turing.haltList machine (true::sign::(Shared.ComplexityBridge.TM2TripleRepack.markers scratch.reverse ++ result))) := by
  induction scratch generalizing result flag with
  | nil =>
    change machine.step (cfg .emit sign flag [] [] [] result) = _
    simpa [Shared.ComplexityBridge.TM2TripleRepack.markers] using emit_nil sign flag result
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,emit_cons]
    simpa [List.reverse_cons,Shared.ComplexityBridge.TM2TripleRepack.markers,List.flatMap_append,List.append_assoc] using ih (true::b::result) (some b)

theorem success_run (name : List Bool) (sign : Bool) :
    runSteps machine.step (2*name.length+3)
      (embed (Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some sign) none [] [] name)) =
      some (Turing.haltList machine (true::sign::BitstringEncoding.delimit name)) := by
  obtain ⟨flag,hc⟩ := collect_loop name [] [false] sign none
  simp only [List.append_nil] at hc
  have he := emit_loop name.reverse [false] sign none
  simp only [List.length_reverse,List.reverse_reverse] at he
  rw [← Shared.ComplexityBridge.TM2TripleRepack.delimit_markers] at he
  have hn : 2*name.length+3 = 1+(name.length+(1+(name.length+1))) := by omega
  rw [hn,runSteps_add]
  change (machine.step (embed (Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some sign) none [] [] name))).bind _ = _
  rw [accept_dispatch]
  change runSteps machine.step (name.length+(1+(name.length+1))) (cfg .collect sign none [] [] name [false]) = _
  rw [runSteps_add,hc]
  change runSteps machine.step (1+(name.length+1)) (cfg .collect sign flag [] name.reverse [] [false]) = _
  rw [runSteps_add]
  change (machine.step (cfg .collect sign flag [] name.reverse [] [false])).bind _ = _
  rw [collect_nil]
  exact he

theorem clearInput_cons (flag : Option Bool) (b : Bool) (input scratch payload : List Bool) :
    machine.step (cfg .clearInput false flag (b::input) scratch payload []) =
      some (cfg .clearInput false (some b) input scratch payload []) := by
  change some (Cfg.mk _ _ (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals (b::input) scratch payload) []) (.inl .input) input)) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem clearInput_nil (flag : Option Bool) (scratch payload : List Bool) :
    machine.step (cfg .clearInput false flag [] scratch payload []) = some (cfg .clearScratch false none [] scratch payload []) := by
  change some (Cfg.mk _ _ (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] scratch payload) []) (.inl .input) [])) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem clearScratch_cons (flag : Option Bool) (b : Bool) (scratch payload : List Bool) :
    machine.step (cfg .clearScratch false flag [] (b::scratch) payload []) = some (cfg .clearScratch false (some b) [] scratch payload []) := by
  change some (Cfg.mk _ _ (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] (b::scratch) payload) []) (.inl .scratch) scratch)) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem clearScratch_nil (flag : Option Bool) (payload : List Bool) :
    machine.step (cfg .clearScratch false flag [] [] payload []) = some (cfg .clearPayload false none [] [] payload []) := by
  change some (Cfg.mk _ _ (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] [] payload) []) (.inl .scratch) [])) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem clearPayload_cons (flag : Option Bool) (b : Bool) (payload : List Bool) :
    machine.step (cfg .clearPayload false flag [] [] (b::payload) []) = some (cfg .clearPayload false (some b) [] [] payload []) := by
  change some (Cfg.mk _ _ (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] [] (b::payload)) []) (.inl .payload) payload)) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem clearPayload_nil (flag : Option Bool) :
    machine.step (cfg .clearPayload false flag [] [] [] []) = some (Turing.haltList machine [false]) := by
  change some (Cfg.mk none (Sum.inl Source.initialState : State) (Function.update (Function.update
    (stackVals (Shared.ComplexityBridge.TM2Undelimit.stackVals [] [] []) []) (.inl .payload) []) (.inr ()) [false])) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update,Turing.haltList,machine]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update,Turing.haltList,machine]

theorem clearInput_loop (input scratch payload : List Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step input.length (cfg .clearInput false flag input scratch payload []) =
      some (cfg .clearInput false flag' [] scratch payload []) := by
  induction input generalizing flag with
  | nil => exact ⟨flag,rfl⟩
  | cons b input ih =>
    obtain ⟨flag',h⟩ := ih (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,clearInput_cons]; exact h

theorem clearScratch_loop (scratch payload : List Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step scratch.length (cfg .clearScratch false flag [] scratch payload []) =
      some (cfg .clearScratch false flag' [] [] payload []) := by
  induction scratch generalizing flag with
  | nil => exact ⟨flag,rfl⟩
  | cons b scratch ih =>
    obtain ⟨flag',h⟩ := ih (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,clearScratch_cons]; exact h

theorem clearPayload_loop (payload : List Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step payload.length (cfg .clearPayload false flag [] [] payload []) =
      some (cfg .clearPayload false flag' [] [] [] []) := by
  induction payload generalizing flag with
  | nil => exact ⟨flag,rfl⟩
  | cons b payload ih =>
    obtain ⟨flag',h⟩ := ih (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,clearPayload_cons]; exact h

theorem clear_run (input scratch payload : List Bool) :
    runSteps machine.step (input.length+scratch.length+payload.length+3) (cfg .clearInput false none input scratch payload []) =
      some (Turing.haltList machine [false]) := by
  obtain ⟨a,ha⟩ := clearInput_loop input scratch payload none
  obtain ⟨b,hb⟩ := clearScratch_loop scratch payload none
  obtain ⟨c,hc⟩ := clearPayload_loop payload none
  have hn : input.length+scratch.length+payload.length+3 = input.length+(1+(scratch.length+(1+(payload.length+1)))) := by omega
  rw [hn,runSteps_add,ha]
  change runSteps machine.step (1+(scratch.length+(1+(payload.length+1)))) (cfg .clearInput false a [] scratch payload []) = _
  rw [runSteps_add]
  change (machine.step (cfg .clearInput false a [] scratch payload [])).bind _ = _
  rw [clearInput_nil]
  change runSteps machine.step (scratch.length+(1+(payload.length+1))) (cfg .clearScratch false none [] scratch payload []) = _
  rw [runSteps_add,hb]
  change runSteps machine.step (1+(payload.length+1)) (cfg .clearScratch false b [] [] payload []) = _
  rw [runSteps_add]
  change (machine.step (cfg .clearScratch false b [] [] payload [])).bind _ = _
  rw [clearScratch_nil]
  change runSteps machine.step (payload.length+1) (cfg .clearPayload false none [] [] payload []) = _
  rw [runSteps_add,hc]
  exact clearPayload_nil c

theorem clearRaw_eq (S : SKey → List Bool) :
    clearRaw S = cfg .clearInput false none (S .input) (S .scratch) (S .payload) [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k
  cases k with
  | inr u => cases u; rfl
  | inl k => cases k <;> rfl

/-- False is failure. Success contains the sign and a self-delimiting raw
name, preserving noncanonical encodings and making the result unambiguous. -/
def encodeResult : Option (List Bool × Bool) → List Bool
  | none => [false]
  | some (name,sign) => true::sign::BitstringEncoding.delimit name

theorem encodeResult_injective : Function.Injective encodeResult := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some q => rcases q with ⟨name,sign⟩; simp [encodeResult] at h
  | some p =>
    rcases p with ⟨name,sign⟩
    cases b with
    | none => simp [encodeResult] at h
    | some q =>
      rcases q with ⟨name',sign'⟩
      have hs : sign = sign' := by simpa [encodeResult] using congrArg (fun x => x.drop 1 |>.head?) h
      have hd : BitstringEncoding.delimit name = BitstringEncoding.delimit name' := by
        simpa [encodeResult] using congrArg (fun x => x.drop 2) h
      have hparse := congrArg (fun x => BitstringEncoding.undelimit (x ++ [])) hd
      simp only [BitstringEncoding.undelimit_delimit,Option.some.injEq,Prod.mk.injEq,true_and] at hparse
      simp [hs,hparse]

def decodeResult (input : List Bool) : List Bool :=
  encodeResult (Shared.ComplexityBridge.TM2LiteralParse.literalBits input)

theorem decodeResult_success_iff (input name : List Bool) (sign : Bool) :
    decodeResult input = true::sign::BitstringEncoding.delimit name ↔
      Shared.ComplexityBridge.TM2LiteralParse.literalBits input = some (name,sign) := by
  change encodeResult (Shared.ComplexityBridge.TM2LiteralParse.literalBits input) = encodeResult (some (name,sign)) ↔ _
  exact ⟨fun h => encodeResult_injective h,fun h => congrArg encodeResult h⟩

theorem decodeResult_failure_iff (input : List Bool) :
    decodeResult input = [false] ↔ Shared.ComplexityBridge.TM2LiteralParse.literalBits input = none := by
  change encodeResult (Shared.ComplexityBridge.TM2LiteralParse.literalBits input) = encodeResult none ↔ _
  exact ⟨fun h => encodeResult_injective h,fun h => congrArg encodeResult h⟩

/-- Failure agrees exactly with the pinned literal decoder, including malformed
signs and incomplete variable delimiters. -/
theorem canonical_failure_iff (input : List Bool) :
    decodeResult input = [false] ↔ (BitstringEncoding.bitDecode input : Option Shared.ComplexityBridge.CNF.Literal) = none := by
  rw [decodeResult_failure_iff,Shared.ComplexityBridge.TM2LiteralParse.literalBits_decode]
  cases Shared.ComplexityBridge.TM2LiteralParse.literalBits input <;> simp

/-- A successful tag preserves the raw name and its decoded literal. -/
theorem canonical_success (input name : List Bool) (sign : Bool)
    (h : decodeResult input = true::sign::BitstringEncoding.delimit name) :
    (BitstringEncoding.bitDecode input : Option Shared.ComplexityBridge.CNF.Literal) =
      some (Computability.decodeNat name,sign) := by
  rw [Shared.ComplexityBridge.TM2LiteralParse.literalBits_decode,(decodeResult_success_iff input name sign).1 h]
  rfl

noncomputable def timePolynomial : Polynomial Nat :=
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let P := Polynomial.C 3*Polynomial.X+Polynomial.C 5
  P+Polynomial.C 1+Polynomial.C 3*(Polynomial.X+P*Polynomial.C D+Polynomial.C 1)

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = (3*n+5)+1+3*(n+(3*n+5)*Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source+1) := by
  simp [timePolynomial]

/-- Both valid and malformed inputs halt with a tagged output. Every source
stack is cleared and the variable framing is emitted with charged cost. -/
theorem total_run (input : List Bool) :
    ∃ t ≤ timePolynomial.eval input.length,
      runSteps machine.step t (Turing.initList machine input) = some (Turing.haltList machine (decodeResult input)) := by
  let P := 3*input.length+5
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let bound := input.length+P*D
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2LiteralParse.parse_progress input
  change n ≤ P at hn
  change runSteps Source.step n (Turing.initList Source input) = some q at hr
  have hterm : terminal q := by
    unfold terminal
    cases hx : Shared.ComplexityBridge.TM2LiteralParse.literalBits input with
    | none =>
      right
      simpa [hx] using hq
    | some p =>
      rcases p with ⟨name,sign⟩
      left
      have he : q = Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some sign) none [] [] name := by simpa [hx] using hq
      rw [he]
      rfl
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step embed terminal stable source_step n (Turing.initList Source input) q hterm hr
  have hstack : ∀ k : SKey, (q.stk k).length ≤ bound := by
    intro k
    have hs := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length Source input n q hr k
    have hm := Nat.mul_le_mul_right D hn
    change (q.stk k).length ≤ input.length+n*D at hs
    dsimp [bound]
    omega
  cases hx : Shared.ComplexityBridge.TM2LiteralParse.literalBits input with
  | none =>
    have hreject : q.l = some (.inr .reject) := by simpa [hx] using hq
    let xs := q.stk .input
    let ys := q.stk .scratch
    let zs := q.stk .payload
    have hxlen : xs.length ≤ bound := hstack .input
    have hylen : ys.length ≤ bound := hstack .scratch
    have hzlen : zs.length ≤ bound := hstack .payload
    have hc := clear_run xs ys zs
    refine ⟨a+1+(xs.length+ys.length+zs.length+3),?_,?_⟩
    · rw [timePolynomial_eval]
      change a+1+(xs.length+ys.length+zs.length+3) ≤ P+1+3*(bound+1)
      omega
    · rw [decodeResult,hx]
      change runSteps machine.step (a+1+(xs.length+ys.length+zs.length+3)) (Turing.initList machine input) = _
      rw [initial_eq,show a+1+(xs.length+ys.length+zs.length+3) = a+(1+(xs.length+ys.length+zs.length+3)) by omega,runSteps_add,har]
      change runSteps machine.step (1+(xs.length+ys.length+zs.length+3)) (embed q) = _
      rw [runSteps_add]
      change (machine.step (embed q)).bind _ = _
      rw [reject_dispatch q hreject,clearRaw_eq]
      exact hc
  | some p =>
    rcases p with ⟨name,sign⟩
    have he : q = Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some sign) none [] [] name := by simpa [hx] using hq
    have hname : name.length ≤ bound := by
      have hp := hstack .payload
      rw [he] at hp
      simpa [Shared.ComplexityBridge.TM2LiteralParse.cfg,Shared.ComplexityBridge.TM2Undelimit.stackVals] using hp
    refine ⟨a+(2*name.length+3),?_,?_⟩
    · rw [timePolynomial_eval]
      change a+(2*name.length+3) ≤ P+1+3*(bound+1)
      omega
    · rw [decodeResult,hx]
      change runSteps machine.step (a+(2*name.length+3)) (Turing.initList machine input) = _
      rw [initial_eq,runSteps_add,har,he]
      exact success_run name sign

/-- Charged raw-bit boundary for the tagged literal parser. -/
noncomputable def rawTimeMachine : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (id : List Bool → List Bool) decodeResult where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun input := by
    let t := Classical.choose (total_run input)
    have ht := (Classical.choose_spec (total_run input)).1
    have hr := (Classical.choose_spec (total_run input)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t] (some (Turing.initList machine (input.map id))) =
        some (Turing.haltList machine ((decodeResult input).map id))
      rw [List.map_id,List.map_id]
      simpa [t] using hr
    · simpa using ht

/-- The total tagged literal parser is polynomial-time under the public
canonical Boolean-list encodings, including malformed input. -/
theorem decodeResult_isPolyTime : ComplexityTheory.IsPolyTime decodeResult := by
  obtain ⟨first⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool) (id : List Bool → List Bool)
    (id : List Bool → List Bool) decodeResult Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine rawTimeMachine
  obtain ⟨second⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool) decodeResult (id : List Bool → List Bool)
    first Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine
  exact ⟨second⟩

namespace Fixtures
example : (runSteps machine.step 8 (Turing.initList machine [false,true])).map
    (fun q => (q.l.isNone,q.stk (.inr ()))) = some (true,[true,true,false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr ()))) (runSteps machine.step 8
    (Turing.initList machine [false,true])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 8 (Turing.initList machine [false])).map
    (fun q => (q.l.isNone,q.stk (.inr ()))) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr ()))) (runSteps machine.step 8
    (Turing.initList machine [false])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 13 (Turing.initList machine [true,false,false,true])).map
    (fun q => (q.l.isNone,q.stk (.inr ()))) = some (true,[true,true,true,false,false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr ()))) (runSteps machine.step 13
    (Turing.initList machine [true,false,false,true])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 9 (Turing.initList machine [false,true,false])).map
    (fun q => (q.l.isNone,q.stk (.inr ()))) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr ()))) (runSteps machine.step 9
    (Turing.initList machine [false,true,false])) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2LiteralOutput
