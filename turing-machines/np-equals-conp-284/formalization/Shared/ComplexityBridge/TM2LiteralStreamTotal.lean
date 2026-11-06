import Shared.ComplexityBridge.TM2LiteralStream
import Shared.ComplexityBridge.TM2GenericStackBound

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2LiteralStreamTotal
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2LiteralStream.machine
abbrev SKey := Shared.ComplexityBridge.TM2LiteralStream.Key
abbrev SourceLabel := Shared.ComplexityBridge.TM2LiteralStream.Label
abbrev SourceState := Shared.ComplexityBridge.TM2LiteralStream.State
abbrev Key := SKey ⊕ Unit
abbrev Label := SourceLabel ⊕ (Unit ⊕ Fin 6)
abbrev State := SourceState ⊕ Option Bool

def sourceState : State → SourceState | .inl v => v | _ => Source.initialState
def flagState : State → Option Bool | .inr v => v | _ => none

def stackVals (S : SKey → List Bool) (out : List Bool) : Key → List Bool
  | .inl k => S k | .inr _ => out
@[simp] theorem stackVals_apply (S : SKey → List Bool) (out : List Bool) (j : SKey) : stackVals S out (.inl j) = S j := rfl

theorem stackVals_update (S : SKey → List Bool) (out : List Bool) (j : SKey) (xs : List Bool) :
    stackVals (Function.update S j xs) out = Function.update (stackVals S out) (.inl j) xs := by
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

def keyOf (i : Fin 5) : SKey :=
  match i.val with | 0 => .stream | 1 => .literal | 2 => .scratch | 3 => .name | _ => .accum
def keyIndex : SKey → Fin 5 | .stream => 0 | .literal => 1 | .scratch => 2 | .name => 3 | .accum => 4
@[simp] theorem keyOf_index (k : SKey) : keyOf (keyIndex k) = k := by cases k <;> rfl
@[simp] theorem index_keyOf (i : Fin 5) : keyIndex (keyOf i) = i := by fin_cases i <;> rfl
def stage (i : Fin 5) : Fin 6 := ⟨i.val,by omega⟩
def next (i : Fin 5) : Fin 6 := ⟨i.val+1,by omega⟩
def done : Fin 6 := ⟨5,by decide⟩

def cleanProgram (i : Fin 6) : Stmt (fun _ : Key => Bool) Label State :=
  if h : i.val < 5 then
    let j : Fin 5 := ⟨i.val,h⟩
    .pop (.inl (keyOf j)) (fun _ x => .inr x)
      (.branch (fun v => (flagState v).isSome) (.goto (fun _ => .inr (.inr i))) (.goto (fun _ => .inr (.inr (next j)))))
  else .push (.inr ()) (fun _ => false) (.load (fun _ => .inl Source.initialState) .halt)

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl (.inl .good) => .load (fun _ => .inr none) (.goto (fun _ => .inr (.inl ())))
  | .inl (.inl .bad) => .load (fun _ => .inr none) (.goto (fun _ => .inr (.inr 0)))
  | .inl l => lift (Shared.ComplexityBridge.TM2LiteralStream.program l)
  | .inr (.inl ()) => .pop (.inl .accum) (fun _ x => .inr x)
      (.branch (fun v => (flagState v).isSome)
        (.push (.inr ()) (fun v => (flagState v).getD false) (.goto (fun _ => .inr (.inl ()))))
        (.push (.inr ()) (fun _ => true) (.load (fun _ => .inl Source.initialState) .halt)))
  | .inr (.inr i) => cleanProgram i

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inl .stream
  k₁ := .inr ()
  Γ := fun _ => Bool
  Λ := Label
  main := .inl Source.main
  σ := State
  initialState := .inl Source.initialState
  m := program

def terminal (q : Source.Cfg) : Prop := q.l = some (.inl .good) ∨ q.l = some (.inl .bad)
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inl Shared.ComplexityBridge.TM2LiteralStream.Phase.good) ∨
      l = some (.inl Shared.ComplexityBridge.TM2LiteralStream.Phase.bad) at h
    rcases h with h | h <;> subst l <;> rfl

theorem source_step (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (embed q) = (Source.step q).map embed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl l => cases l with
        | good => exact False.elim (h (Or.inl rfl))
        | bad => exact False.elim (h (Or.inr rfl))
        | start | copy =>
          change some (stepAux (lift (Shared.ComplexityBridge.TM2LiteralStream.program _)) (.inl v) (stackVals S [])) = _
          rw [lift_aux]; rfl
      | inr l =>
        change some (stepAux (lift (Shared.ComplexityBridge.TM2LiteralStream.program (.inr l))) (.inl v) (stackVals S [])) = _
        rw [lift_aux]; rfl

theorem initial_eq (bits : List Bool) : Turing.initList machine bits = embed (Turing.initList Source bits) := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k
  cases k with
  | inr u => cases u; simp [machine,embed,stackVals,Turing.initList]
  | inl k => cases k <;> simp [machine,embed,stackVals,Turing.initList,Source,Shared.ComplexityBridge.TM2LiteralStream.machine] <;> rfl

def restoreCfg (flag : Option Bool) (accum out : List Bool) : machine.Cfg :=
  ⟨some (.inr (.inl ())),.inr flag,stackVals (Shared.ComplexityBridge.TM2LiteralStream.stackVals [] [] [] [] accum) out⟩
def cleanCfg (i : Fin 6) (flag : Option Bool) (S : SKey → List Bool) : machine.Cfg :=
  ⟨some (.inr (.inr i)),.inr flag,stackVals S []⟩

theorem good_dispatch (accum : List Bool) :
    machine.step (embed (Shared.ComplexityBridge.TM2LiteralStream.cfg .good none [] [] [] [] accum)) =
      some (restoreCfg none accum []) := by rfl

theorem bad_dispatch (q : Source.Cfg) (h : q.l = some (.inl .bad)) :
    machine.step (embed q) = some (cleanCfg 0 none q.stk) := by
  cases q with
  | mk l v S =>
    change l = some (.inl Shared.ComplexityBridge.TM2LiteralStream.Phase.bad) at h
    subst l; rfl

theorem restore_cons (flag : Option Bool) (b : Bool) (accum out : List Bool) :
    machine.step (restoreCfg flag (b::accum) out) = some (restoreCfg (some b) accum (b::out)) := by
  change some (Cfg.mk _ _ (Function.update (Function.update
    (stackVals (Shared.ComplexityBridge.TM2LiteralStream.stackVals [] [] [] [] (b::accum)) out) (.inl .accum) accum)
      (.inr ()) (b::out))) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2LiteralStream.stackVals,Function.update]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2LiteralStream.stackVals,Function.update]

theorem restore_nil (flag : Option Bool) (out : List Bool) :
    machine.step (restoreCfg flag [] out) = some (Turing.haltList machine (true::out)) := by
  change some (Cfg.mk none (Sum.inl Source.initialState : State) (Function.update (Function.update
    (stackVals (Shared.ComplexityBridge.TM2LiteralStream.stackVals [] [] [] [] []) out) (.inl .accum) [])
      (.inr ()) (true::out))) = _
  congr 1; congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Shared.ComplexityBridge.TM2LiteralStream.stackVals,Function.update,Turing.haltList,machine]
  | inl k => cases k <;> simp [stackVals,Shared.ComplexityBridge.TM2LiteralStream.stackVals,Function.update,Turing.haltList,machine]

theorem restore_run (accum out : List Bool) (flag : Option Bool) :
    runSteps machine.step (accum.length+1) (restoreCfg flag accum out) =
      some (Turing.haltList machine (true::(accum.reverse++out))) := by
  induction accum generalizing out flag with
  | nil =>
    change machine.step (restoreCfg flag [] out) = _
    simpa using restore_nil flag out
  | cons b accum ih =>
    rw [List.length_cons,show accum.length+1+1 = (accum.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::out) (some b)

theorem clean_cons (i : Fin 5) (flag : Option Bool) (S : SKey → List Bool) (b : Bool) (xs : List Bool) :
    machine.step (cleanCfg (stage i) flag (Function.update S (keyOf i) (b::xs))) =
      some (cleanCfg (stage i) (some b) (Function.update S (keyOf i) xs)) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,flagState,stackVals_apply,Function.update_self,List.head?_cons,Option.isSome_some,List.tail_cons,Bool.cond_true]
  congr 1; congr 1
  rw [← stackVals_update,Function.update_idem]

theorem clean_nil (i : Fin 5) (flag : Option Bool) (S : SKey → List Bool) :
    machine.step (cleanCfg (stage i) flag (Function.update S (keyOf i) [])) =
      some (cleanCfg (next i) none (Function.update S (keyOf i) [])) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,flagState,stackVals_apply,Function.update_self,List.head?_nil,Option.isSome_none,List.tail_nil,Bool.cond_false]
  congr 1; congr 1
  rw [← stackVals_update,Function.update_idem]

theorem sweep_one (i : Fin 5) (flag : Option Bool) (S : SKey → List Bool) (xs : List Bool) :
    runSteps machine.step (xs.length+1) (cleanCfg (stage i) flag (Function.update S (keyOf i) xs)) =
      some (cleanCfg (next i) none (Function.update S (keyOf i) [])) := by
  induction xs generalizing flag with
  | nil => exact clean_nil i flag S
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,clean_cons]
    exact ih (some b)

theorem sweep_suffix (bound n : Nat) :
    ∀ (a : Nat) (ha : a+n = 5) (S : SKey → List Bool) (flag : Option Bool),
      (∀ k, (keyIndex k).val < a → S k = []) → (∀ k, (S k).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps machine.step t (cleanCfg ⟨a,by omega⟩ flag S) = some (cleanCfg done f (fun _ => [])) := by
  induction n with
  | zero =>
    intro a ha S flag hempty hbound
    have ae : a = 5 := by omega
    have hS : S = fun _ => [] := by
      funext k; apply hempty; have hk := (keyIndex k).isLt; omega
    subst S
    have hl : (⟨a,by omega⟩ : Fin 6) = done := by apply Fin.ext; simp [done,ae]
    refine ⟨0,by simp,flag,?_⟩
    rw [hl]; rfl
  | succ n ih =>
    intro a ha S flag hempty hbound
    have halt : a < 5 := by omega
    let i : Fin 5 := ⟨a,halt⟩
    let S' := Function.update S (keyOf i) []
    have hempty' : ∀ k, (keyIndex k).val < a+1 → S' k = [] := by
      intro k hk
      by_cases heq : k = keyOf i
      · subst k; simp [S']
      · have hval : (keyIndex k).val ≠ a := by
          intro hv
          have hi : keyIndex k = i := Fin.ext hv
          apply heq
          calc
            k = keyOf (keyIndex k) := by simp
            _ = keyOf i := by rw [hi]
        have hlt : (keyIndex k).val < a := by omega
        simpa [S',Function.update_of_ne heq] using hempty k hlt
    have hbound' : ∀ k, (S' k).length ≤ bound := by
      intro k
      by_cases heq : k = keyOf i
      · subst k; simp [S']
      · simpa [S',Function.update_of_ne heq] using hbound k
    obtain ⟨t,ht,f,hrun⟩ := ih (a+1) (by omega) S' none hempty' hbound'
    have hstage : stage i = (⟨a,by omega⟩ : Fin 6) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Fin 6) := by apply Fin.ext; rfl
    have hone := sweep_one i flag S (S (keyOf i))
    rw [Function.update_eq_self,hstage,hnext] at hone
    have htbound : (S (keyOf i)).length+1+t ≤ (n+1)*(bound+1) := by
      have hi := hbound (keyOf i)
      rw [Nat.add_mul,Nat.one_mul]; omega
    refine ⟨(S (keyOf i)).length+1+t,by simpa using htbound,f,?_⟩
    rw [runSteps_add,hone]
    exact hrun

theorem finish (flag : Option Bool) :
    machine.step (cleanCfg done flag (fun _ => [])) = some (Turing.haltList machine [false]) := by
  have hn : ¬done.val < 5 := by simp [done]
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,dif_neg hn,stepAux]
  congr 1
  change Cfg.mk none (Sum.inl Source.initialState : State)
    (Function.update (stackVals (fun _ => []) []) (.inr ()) [false]) = _
  congr 1; funext k
  cases k with
  | inr u => cases u; simp [stackVals,Function.update,Turing.haltList,machine]
  | inl k => cases k <;> simp [stackVals,Function.update,Turing.haltList,machine]

theorem sweep_all (S : SKey → List Bool) (bound : Nat) (hbound : ∀ k, (S k).length ≤ bound) :
    ∃ t ≤ 5*(bound+1)+1, runSteps machine.step t (cleanCfg 0 none S) = some (Turing.haltList machine [false]) := by
  obtain ⟨t,ht,flag,hr⟩ := sweep_suffix bound 5 0 (by omega) S none (by intro k hk; omega) hbound
  refine ⟨t+1,by omega,?_⟩
  change runSteps machine.step (t+1) (cleanCfg ⟨0,by omega⟩ none S) = _
  rw [runSteps_add,hr]
  exact finish flag

/-- A failure tag or the framed raw variable-name sequence. -/
def decodeResult (input : List Bool) : List Bool :=
  match Shared.ComplexityBridge.TM2LiteralStream.parseNames input with
  | none => [false]
  | some names => true::Shared.ComplexityBridge.TM2WitnessLookup.frames names

noncomputable def timePolynomial : Polynomial Nat :=
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let P := Polynomial.X*(Polynomial.C 7*Polynomial.X+Polynomial.C 11)+Polynomial.C 1
  P+Polynomial.C 1+Polynomial.C 5*(Polynomial.X+P*Polynomial.C D+Polynomial.C 1)+Polynomial.C 1

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = (n*(7*n+11)+1)+1+5*(n+(n*(7*n+11)+1)*Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source+1)+1 := by
  simp [timePolynomial]

/-- The finite loop and both cleanup branches halt with the exact tagged
result for every raw occurrence stream, within one explicit polynomial. -/
theorem total_run (input : List Bool) :
    ∃ t ≤ timePolynomial.eval input.length,
      runSteps machine.step t (Turing.initList machine input) = some (Turing.haltList machine (decodeResult input)) := by
  let P := input.length*(7*input.length+11)+1
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let bound := input.length+P*D
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2LiteralStream.parse_progress input
  change n ≤ P at hn
  change runSteps Source.step n (Turing.initList Source input) = some q at hr
  have hterm : terminal q := by
    unfold terminal
    cases hx : Shared.ComplexityBridge.TM2LiteralStream.parseNames input with
    | none => right; simpa [hx] using hq
    | some names =>
      left
      have he : q = Shared.ComplexityBridge.TM2LiteralStream.cfg .good none [] [] [] [] (Shared.ComplexityBridge.TM2WitnessLookup.frames names).reverse := by simpa [hx] using hq
      rw [he]; rfl
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step embed terminal stable source_step n (Turing.initList Source input) q hterm hr
  have hstack : ∀ k : SKey, (q.stk k).length ≤ bound := by
    intro k
    have hs := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length Source input n q hr k
    have hm := Nat.mul_le_mul_right D hn
    change (q.stk k).length ≤ input.length+n*D at hs
    dsimp [bound]; omega
  cases hx : Shared.ComplexityBridge.TM2LiteralStream.parseNames input with
  | none =>
    have hbad : q.l = some (.inl .bad) := by simpa [hx] using hq
    obtain ⟨b,hb,hbr⟩ := sweep_all q.stk bound hstack
    refine ⟨a+1+b,?_,?_⟩
    · rw [timePolynomial_eval]
      change a+1+b ≤ P+1+5*(bound+1)+1
      omega
    · rw [decodeResult,hx]
      change runSteps machine.step (a+1+b) (Turing.initList machine input) = _
      rw [initial_eq,show a+1+b = a+(1+b) by omega,runSteps_add,har]
      change runSteps machine.step (1+b) (embed q) = _
      rw [runSteps_add]
      change (machine.step (embed q)).bind _ = _
      rw [bad_dispatch q hbad]
      exact hbr
  | some names =>
    let frames := Shared.ComplexityBridge.TM2WitnessLookup.frames names
    have he : q = Shared.ComplexityBridge.TM2LiteralStream.cfg .good none [] [] [] [] frames.reverse := by simpa [hx,frames] using hq
    have hlen : frames.length ≤ bound := by
      have hs := hstack .accum
      rw [he] at hs
      simpa [Shared.ComplexityBridge.TM2LiteralStream.cfg,Shared.ComplexityBridge.TM2LiteralStream.stackVals,List.length_reverse] using hs
    have hrestore := restore_run frames.reverse [] none
    simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hrestore
    refine ⟨a+1+(frames.length+1),?_,?_⟩
    · rw [timePolynomial_eval]
      change a+1+(frames.length+1) ≤ P+1+5*(bound+1)+1
      omega
    · rw [decodeResult,hx]
      change runSteps machine.step (a+1+(frames.length+1)) (Turing.initList machine input) = _
      rw [initial_eq,show a+1+(frames.length+1) = a+(1+(frames.length+1)) by omega,runSteps_add,har,he]
      change runSteps machine.step (1+(frames.length+1)) (embed (Shared.ComplexityBridge.TM2LiteralStream.cfg .good none [] [] [] [] frames.reverse)) = _
      rw [runSteps_add]
      change (machine.step (embed (Shared.ComplexityBridge.TM2LiteralStream.cfg .good none [] [] [] [] frames.reverse))).bind _ = _
      rw [good_dispatch]
      exact hrestore

/-- Charged raw-bit boundary for the literal occurrence parser. -/
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

/-- Total occurrence extraction is polynomial-time under the public canonical
Boolean-list encodings, including malformed inputs. -/
theorem decodeResult_isPolyTime : ComplexityTheory.IsPolyTime decodeResult := by
  obtain ⟨first⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool) (id : List Bool → List Bool)
    (id : List Bool → List Bool) decodeResult Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine rawTimeMachine
  obtain ⟨second⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool) decodeResult (id : List Bool → List Bool)
    first Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine
  exact ⟨second⟩

/-- Successful canonical CNF parsing supplies an occurrence stream on which
this total extractor returns exactly the verifier's names. -/
theorem cnf_occurrences (input : List Bool) (formula : Shared.ComplexityBridge.CNF.Formula)
    (h : Shared.ComplexityBridge.CNF.parse input = some formula) :
    ∃ literalStream rawNames,
      Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult input = true::literalStream ∧
      rawNames.map Computability.decodeNat = Shared.ComplexityBridge.CNF.variableOccurrences formula ∧
      decodeResult literalStream = true::Shared.ComplexityBridge.TM2WitnessLookup.frames rawNames := by
  obtain ⟨clauses,groups,pairs,hc,hg,hn,hvars,hflat⟩ :=
    Shared.ComplexityBridge.CNFFlattenBridge.parse_occurrences_correct input formula h
  let literalStream := Shared.ComplexityBridge.TM2WitnessLookup.frames groups.flatten
  let rawNames := pairs.map Prod.fst
  have hp : Shared.ComplexityBridge.TM2LiteralStream.parseNames literalStream = some rawNames := by
    dsimp [literalStream,rawNames]
    rw [Shared.ComplexityBridge.TM2LiteralStream.parseNames_framed,hn]
    rfl
  refine ⟨literalStream,rawNames,hflat,hvars,?_⟩
  simp [decodeResult,hp]

namespace Fixtures
example : (runSteps machine.step 3 (Turing.initList machine [])).map
    (fun q => (q.l.isNone,q.stk (.inr ()))) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr ()))) (runSteps machine.step 3 (Turing.initList machine [])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 11 (Turing.initList machine [true])).map
    (fun q => (q.l.isNone,q.stk (.inr ()))) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr ()))) (runSteps machine.step 11 (Turing.initList machine [true])) : Option (Bool × List Bool)) = _
  decide
set_option maxRecDepth 4096 in
example : (runSteps machine.step 51 (Turing.initList machine
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[true,false,false,true],[false,false]]))).map
    (fun q => (q.l.isNone,q.stk (.inr ()))) = some (true,[true,true,false,false,false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr ()))) (runSteps machine.step 51
    (Turing.initList machine (Shared.ComplexityBridge.TM2WitnessLookup.frames [[true,false,false,true],[false,false]]))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2LiteralStreamTotal
