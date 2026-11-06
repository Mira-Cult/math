import Shared.ComplexityBridge.CNFOccurrences
import Shared.ComplexityBridge.TM2GenericStackBound

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2CNFValidate
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Outer := Shared.ComplexityBridge.TM2Undelimit.machine
abbrev Inner := Shared.ComplexityBridge.TM2LiteralStream.machine
abbrev OKey := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev IKey := Shared.ComplexityBridge.TM2LiteralStream.Key
abbrev OLabel := Shared.ComplexityBridge.TM2Undelimit.Label
abbrev ILabel := Shared.ComplexityBridge.TM2LiteralStream.Label
abbrev IState := Shared.ComplexityBridge.TM2LiteralStream.State
inductive Key where | stream | clause | outerScratch | litInput | litScratch | litName | litAccum deriving DecidableEq
inductive Phase where | start | clear | good | bad deriving DecidableEq
instance : Fintype Key := Fintype.ofList [.stream,.clause,.outerScratch,.litInput,.litScratch,.litName,.litAccum] (by intro k; cases k <;> simp)
instance : Fintype Phase := Fintype.ofList [.start,.clear,.good,.bad] (by intro p; cases p <;> simp)
abbrev Label := Phase ⊕ (OLabel ⊕ ILabel)
abbrev State := Option Bool ⊕ (IState ⊕ Option Bool)
def outerState : State → Option Bool | .inl v => v | _ => none
def innerState : State → IState | .inr (.inl v) => v | _ => Inner.initialState
def flagState : State → Option Bool | .inr (.inr v) => v | _ => none

def okey : OKey → Key | .input => .stream | .scratch => .outerScratch | .payload => .clause
def ikey : IKey → Key | .stream => .clause | .literal => .litInput | .scratch => .litScratch | .name => .litName | .accum => .litAccum
def ostacks (S : OKey → List Bool) (other : Key → List Bool) : Key → List Bool
  | .stream => S .input | .outerScratch => S .scratch | .clause => S .payload | k => other k
def istacks (S : IKey → List Bool) (other : Key → List Bool) : Key → List Bool
  | .clause => S .stream | .litInput => S .literal | .litScratch => S .scratch | .litName => S .name | .litAccum => S .accum | k => other k
@[simp] theorem ostacks_apply (S : OKey → List Bool) (other : Key → List Bool) (j : OKey) : ostacks S other (okey j) = S j := by cases j <;> rfl
@[simp] theorem istacks_apply (S : IKey → List Bool) (other : Key → List Bool) (j : IKey) : istacks S other (ikey j) = S j := by cases j <;> rfl

theorem oupdate (S : OKey → List Bool) (other : Key → List Bool) (j : OKey) (xs : List Bool) :
    ostacks (Function.update S j xs) other = Function.update (ostacks S other) (okey j) xs := by
  funext k; cases j <;> cases k <;> simp [ostacks,okey,Function.update]
theorem iupdate (S : IKey → List Bool) (other : Key → List Bool) (j : IKey) (xs : List Bool) :
    istacks (Function.update S j xs) other = Function.update (istacks S other) (ikey j) xs := by
  funext k; cases j <;> cases k <;> simp [istacks,ikey,Function.update]

def outerEmbed (other : Key → List Bool) (q : Outer.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),.inl q.var,ostacks q.stk other⟩
def innerEmbed (other : Key → List Bool) (q : Inner.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inr l)),.inr (.inl q.var),istacks q.stk other⟩

def liftOuter : Stmt (fun _ : OKey => Bool) OLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (okey j) (fun v => f (outerState v)) (liftOuter q)
  | .peek j f q => .peek (okey j) (fun v h => .inl (f (outerState v) h)) (liftOuter q)
  | .pop j f q => .pop (okey j) (fun v h => .inl (f (outerState v) h)) (liftOuter q)
  | .load f q => .load (fun v => .inl (f (outerState v))) (liftOuter q)
  | .branch f q r => .branch (fun v => f (outerState v)) (liftOuter q) (liftOuter r)
  | .goto f => .goto (fun v => .inr (.inl (f (outerState v))))
  | .halt => .halt

def liftInner : Stmt (fun _ : IKey => Bool) ILabel IState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (ikey j) (fun v => f (innerState v)) (liftInner q)
  | .peek j f q => .peek (ikey j) (fun v h => .inr (.inl (f (innerState v) h))) (liftInner q)
  | .pop j f q => .pop (ikey j) (fun v h => .inr (.inl (f (innerState v) h))) (liftInner q)
  | .load f q => .load (fun v => .inr (.inl (f (innerState v)))) (liftInner q)
  | .branch f q r => .branch (fun v => f (innerState v)) (liftInner q) (liftInner r)
  | .goto f => .goto (fun v => .inr (.inr (f (innerState v))))
  | .halt => .halt

theorem liftOuter_aux (q : Outer.Stmt) (v : Option Bool) (S : OKey → List Bool) (other : Key → List Bool) :
    stepAux (liftOuter q) (.inl v) (ostacks S other) = outerEmbed other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => simp only [liftOuter,stepAux,outerState,ostacks_apply]; rw [← oupdate S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftOuter,stepAux,outerState,ostacks_apply]; exact ih _ _
  | pop j f q ih => simp only [liftOuter,stepAux,outerState,ostacks_apply]; rw [← oupdate S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftOuter,stepAux,outerState,h,ihq,ihr]

theorem liftInner_aux (q : Inner.Stmt) (v : IState) (S : IKey → List Bool) (other : Key → List Bool) :
    stepAux (liftInner q) (.inr (.inl v)) (istacks S other) = innerEmbed other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => simp only [liftInner,stepAux,innerState,istacks_apply]; rw [← iupdate S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftInner,stepAux,innerState,istacks_apply]; exact ih _ _
  | pop j f q ih => simp only [liftInner,stepAux,innerState,istacks_apply]; rw [← iupdate S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftInner,stepAux,innerState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .start => .peek .stream (fun _ h => .inr (.inr h))
      (.branch (fun v => (flagState v).isSome)
        (.load (fun _ => .inl none) (.goto (fun _ => .inr (.inl .header))))
        (.goto (fun _ => .inl .good)))
  | .inl .clear => .pop .litAccum (fun _ h => .inr (.inr h))
      (.branch (fun v => (flagState v).isSome) (.goto (fun _ => .inl .clear)) (.goto (fun _ => .inl .start)))
  | .inl .good => .goto (fun _ => .inl .good)
  | .inl .bad => .goto (fun _ => .inl .bad)
  | .inr (.inl .done) => .load (fun _ => .inr (.inl Inner.initialState)) (.goto (fun _ => .inr (.inr Inner.main)))
  | .inr (.inl .reject) => .goto (fun _ => .inl .bad)
  | .inr (.inl l) => liftOuter (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr (.inr (.inl .good)) => .load (fun _ => .inr (.inr none)) (.goto (fun _ => .inl .clear))
  | .inr (.inr (.inl .bad)) => .goto (fun _ => .inl .bad)
  | .inr (.inr l) => liftInner (Shared.ComplexityBridge.TM2LiteralStream.program l)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .stream
  k₁ := .litAccum
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .start
  σ := State
  initialState := .inr (.inr none)
  m := program

def outerTerminal (q : Outer.Cfg) : Prop := q.l = some .done ∨ q.l = some .reject
noncomputable instance : DecidablePred outerTerminal := fun _ => Classical.propDecidable _
theorem outer_stable (q : Outer.Cfg) (h : outerTerminal q) : Outer.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.done ∨ l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    rcases h with h | h <;> subst l <;> rfl

theorem outer_step (other : Key → List Bool) (q : Outer.Cfg) (h : ¬ outerTerminal q) :
    machine.step (outerEmbed other q) = (Outer.step q).map (outerEmbed other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | done => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | header | data | restore =>
        change some (stepAux (liftOuter (Shared.ComplexityBridge.TM2Undelimit.program _)) (.inl v) (ostacks S other)) = _
        rw [liftOuter_aux]; rfl

def innerTerminal (q : Inner.Cfg) : Prop := q.l = some (.inl .good) ∨ q.l = some (.inl .bad)
noncomputable instance : DecidablePred innerTerminal := fun _ => Classical.propDecidable _
theorem inner_stable (q : Inner.Cfg) (h : innerTerminal q) : Inner.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inl Shared.ComplexityBridge.TM2LiteralStream.Phase.good) ∨
      l = some (.inl Shared.ComplexityBridge.TM2LiteralStream.Phase.bad) at h
    rcases h with h | h <;> subst l <;> rfl

theorem inner_step (other : Key → List Bool) (q : Inner.Cfg) (h : ¬ innerTerminal q) :
    machine.step (innerEmbed other q) = (Inner.step q).map (innerEmbed other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl l => cases l with
        | good => exact False.elim (h (Or.inl rfl))
        | bad => exact False.elim (h (Or.inr rfl))
        | start | copy =>
          change some (stepAux (liftInner (Shared.ComplexityBridge.TM2LiteralStream.program _)) (.inr (.inl v)) (istacks S other)) = _
          rw [liftInner_aux]; rfl
      | inr l =>
        change some (stepAux (liftInner (Shared.ComplexityBridge.TM2LiteralStream.program (.inr l))) (.inr (.inl v)) (istacks S other)) = _
        rw [liftInner_aux]; rfl

def stackVals (stream clause outerScratch litInput litScratch litName litAccum : List Bool) : Key → List Bool
  | .stream => stream | .clause => clause | .outerScratch => outerScratch | .litInput => litInput
  | .litScratch => litScratch | .litName => litName | .litAccum => litAccum

def cfg (l : Phase) (flag : Option Bool) (stream accum : List Bool) : machine.Cfg :=
  ⟨some (.inl l),.inr (.inr flag),stackVals stream [] [] [] [] [] accum⟩

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .start none input [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals,Turing.initList] <;> rfl

theorem start_nil (flag : Option Bool) : machine.step (cfg .start flag [] []) = some (cfg .good none [] []) := by rfl

theorem start_cons (flag : Option Bool) (b : Bool) (tail : List Bool) :
    machine.step (cfg .start flag (b::tail) []) = some (outerEmbed (fun _ => []) (Turing.initList Outer (b::tail))) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [outerEmbed,ostacks,stackVals,Turing.initList,Outer,Shared.ComplexityBridge.TM2Undelimit.machine] <;> rfl

theorem start_delimit (payload tail : List Bool) (flag : Option Bool) :
    machine.step (cfg .start flag (BitstringEncoding.delimit payload ++ tail) []) =
      some (outerEmbed (fun _ => []) (Turing.initList Outer (BitstringEncoding.delimit payload ++ tail))) := by
  cases payload with
  | nil => exact start_cons flag false tail
  | cons b payload => exact start_cons flag true (b::BitstringEncoding.delimit payload ++ tail)

theorem outer_done (tail clause : List Bool) :
    machine.step (outerEmbed (fun _ => []) (Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] clause)) =
      some (innerEmbed (stackVals tail [] [] [] [] [] []) (Turing.initList Inner clause)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [outerEmbed,innerEmbed,ostacks,istacks,stackVals,
    Shared.ComplexityBridge.TM2Undelimit.cfg,Shared.ComplexityBridge.TM2Undelimit.stackVals,
    Turing.initList,Inner,Shared.ComplexityBridge.TM2LiteralStream.machine] <;> rfl

theorem inner_good (tail accum : List Bool) :
    machine.step (innerEmbed (stackVals tail [] [] [] [] [] []) (Shared.ComplexityBridge.TM2LiteralStream.cfg .good none [] [] [] [] accum)) =
      some (cfg .clear none tail accum) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> rfl

theorem clear_cons (flag : Option Bool) (b : Bool) (tail accum : List Bool) :
    machine.step (cfg .clear flag tail (b::accum)) = some (cfg .clear (some b) tail accum) := by
  change some (Cfg.mk _ _ (Function.update (stackVals tail [] [] [] [] [] (b::accum)) .litAccum accum)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem clear_nil (flag : Option Bool) (tail : List Bool) :
    machine.step (cfg .clear flag tail []) = some (cfg .start none tail []) := by
  change some (Cfg.mk _ _ (Function.update (stackVals tail [] [] [] [] [] []) .litAccum [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem clear_run (tail accum : List Bool) (flag : Option Bool) :
    runSteps machine.step (accum.length+1) (cfg .clear flag tail accum) = some (cfg .start none tail []) := by
  induction accum generalizing flag with
  | nil => exact clear_nil flag tail
  | cons b accum ih =>
    rw [List.length_cons,show accum.length+1+1 = (accum.length+1)+1 by omega,runSteps_front,clear_cons]
    exact ih (some b)

theorem outer_rejected (q : Outer.Cfg) (h : q.l = some .reject) :
    ∃ r, machine.step (outerEmbed (fun _ => []) q) = some r ∧ r.l = some (.inl .bad) := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    subst l
    exact ⟨⟨some (.inl .bad),.inl v,ostacks S (fun _ => [])⟩,rfl,rfl⟩

theorem inner_rejected (q : Inner.Cfg) (tail : List Bool) (h : q.l = some (.inl .bad)) :
    ∃ r, machine.step (innerEmbed (stackVals tail [] [] [] [] [] []) q) = some r ∧ r.l = some (.inl .bad) := by
  cases q with
  | mk l v S =>
    change l = some (.inl Shared.ComplexityBridge.TM2LiteralStream.Phase.bad) at h
    subst l
    exact ⟨⟨some (.inl .bad),.inr (.inl v),istacks S (stackVals tail [] [] [] [] [] [])⟩,rfl,rfl⟩

/-- Definedness of elementwise optional parsing is exactly a finite all-test. -/
theorem mapM_isSome {α β : Type} (f : α → Option β) (xs : List α) :
    (xs.mapM f).isSome = xs.all (fun x => (f x).isSome) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x with
    | none => simp [List.mapM_cons,h]
    | some y =>
      cases ht : xs.mapM f <;> simp_all [List.mapM_cons]

theorem literal_defined (raw : List Bool) :
    (Shared.ComplexityBridge.TM2LiteralParse.literalBits raw).isSome =
      (BitstringEncoding.bitDecode raw : Option Shared.ComplexityBridge.CNF.Literal).isSome := by
  rw [Shared.ComplexityBridge.TM2LiteralParse.literalBits_decode]
  cases Shared.ComplexityBridge.TM2LiteralParse.literalBits raw <;> rfl

/-- The literal-stream parser accepts precisely the raw clauses accepted by
the public CNF clause decoder. -/
theorem clause_defined (raw : List Bool) :
    (Shared.ComplexityBridge.TM2LiteralStream.parseNames raw).isSome =
      (BitstringEncoding.bitDecode raw : Option Shared.ComplexityBridge.CNF.Clause).isSome := by
  rw [Shared.ComplexityBridge.TM2LiteralStream.parseNames_correct]
  change ((BitstringEncoding.undelimitBlocks raw).bind
    (fun lits => (lits.mapM Shared.ComplexityBridge.TM2LiteralParse.literalBits).map (List.map Prod.fst))).isSome =
      ((BitstringEncoding.undelimitBlocks raw).bind (List.mapM (BitstringEncoding.bitDecode (α := Shared.ComplexityBridge.CNF.Literal)))).isSome
  cases h : BitstringEncoding.undelimitBlocks raw with
  | none => rfl
  | some lits =>
    simp only [Option.bind_some]
    cases hv : lits.mapM Shared.ComplexityBridge.TM2LiteralParse.literalBits with
    | none =>
      have hAll := mapM_isSome Shared.ComplexityBridge.TM2LiteralParse.literalBits lits
      have hOther := mapM_isSome (BitstringEncoding.bitDecode (α := Shared.ComplexityBridge.CNF.Literal)) lits
      have he : lits.all (fun x => (Shared.ComplexityBridge.TM2LiteralParse.literalBits x).isSome) =
          lits.all (fun x => (BitstringEncoding.bitDecode x : Option Shared.ComplexityBridge.CNF.Literal).isSome) := by
        congr 1; funext x; exact literal_defined x
      rw [hv] at hAll
      simp only [Option.isSome_none] at hAll
      rw [← he,← hAll] at hOther
      cases hz : lits.mapM (BitstringEncoding.bitDecode (α := Shared.ComplexityBridge.CNF.Literal)) <;> simp_all
    | some names =>
      have hAll := mapM_isSome Shared.ComplexityBridge.TM2LiteralParse.literalBits lits
      have hOther := mapM_isSome (BitstringEncoding.bitDecode (α := Shared.ComplexityBridge.CNF.Literal)) lits
      have he : lits.all (fun x => (Shared.ComplexityBridge.TM2LiteralParse.literalBits x).isSome) =
          lits.all (fun x => (BitstringEncoding.bitDecode x : Option Shared.ComplexityBridge.CNF.Literal).isSome) := by
        congr 1; funext x; exact literal_defined x
      rw [hv] at hAll
      simp only [Option.isSome_some] at hAll
      rw [← he,← hAll] at hOther
      cases hz : lits.mapM (BitstringEncoding.bitDecode (α := Shared.ComplexityBridge.CNF.Literal)) <;> simp_all

noncomputable def iterationPolynomial : Polynomial Nat :=
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Inner
  Polynomial.C (D+1)*(Polynomial.X*(Polynomial.C 7*Polynomial.X+Polynomial.C 11)+Polynomial.C 1)+Polynomial.C 4*Polynomial.X+Polynomial.C 10

theorem iterationPolynomial_eval (n : Nat) :
    iterationPolynomial.eval n = (Shared.ComplexityBridge.TM2GenericStackBound.tableBound Inner+1)*(n*(7*n+11)+1)+4*n+10 := by
  simp [iterationPolynomial]

/-- Validate one clause while preserving the outer tail; successful inner
parsing is fully charged, and its temporary occurrence stack is cleared. -/
theorem process_one (clause tail : List Bool) (flag : Option Bool) (names : List (List Bool))
    (hvalid : Shared.ComplexityBridge.TM2LiteralStream.parseNames clause = some names) :
    ∃ t ≤ iterationPolynomial.eval (BitstringEncoding.delimit clause ++ tail).length,
      runSteps machine.step t (cfg .start flag (BitstringEncoding.delimit clause ++ tail) []) = some (cfg .start none tail []) := by
  let input := BitstringEncoding.delimit clause ++ tail
  let outerEnd := Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] clause
  let innerOther := stackVals tail [] [] [] [] [] []
  let innerEnd := Shared.ComplexityBridge.TM2LiteralStream.cfg .good none [] [] [] [] (Shared.ComplexityBridge.TM2WitnessLookup.frames names).reverse
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Inner
  let P := clause.length*(7*clause.length+11)+1
  let accum := (Shared.ComplexityBridge.TM2WitnessLookup.frames names).reverse
  have hp := Shared.ComplexityBridge.TM2Undelimit.valid_run clause tail
  change runSteps Outer.step (3*clause.length+2) (Turing.initList Outer input) = some outerEnd at hp
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed (fun _ => [])) outerTerminal outer_stable (outer_step (fun _ => []))
    _ (Turing.initList Outer input) outerEnd (Or.inl rfl) hp
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2LiteralStream.parse_progress clause
  change n ≤ P at hn
  have he : q = innerEnd := by simpa [hvalid,innerEnd,accum] using hq
  subst q
  change runSteps Inner.step n (Turing.initList Inner clause) = some innerEnd at hr
  have hacc := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length Inner clause n innerEnd hr .accum
  have hm := Nat.mul_le_mul_right D hn
  have hacc' : accum.length ≤ clause.length+P*D := by
    change accum.length ≤ clause.length+n*D at hacc
    omega
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Inner.step machine.step (innerEmbed innerOther) innerTerminal inner_stable (inner_step innerOther)
    n (Turing.initList Inner clause) innerEnd (Or.inl rfl) hr
  have hin : clause.length ≤ input.length := by simp only [input,List.length_append,BitstringEncoding.length_delimit]; omega
  have hpoly := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono iterationPolynomial hin
  refine ⟨1+a+1+b+1+(accum.length+1),?_,?_⟩
  · have hlocal : 1+a+1+b+1+(accum.length+1) ≤ iterationPolynomial.eval clause.length := by
      rw [iterationPolynomial_eval]
      change 1+a+1+b+1+(accum.length+1) ≤ (D+1)*P+4*clause.length+10
      rw [Nat.add_mul,Nat.one_mul]
      have hcomm : D*P = P*D := Nat.mul_comm D P
      omega
    exact le_trans hlocal hpoly
  · rw [show 1+a+1+b+1+(accum.length+1) = 1+(a+(1+(b+(1+(accum.length+1))))) by omega,runSteps_add]
    change (machine.step (cfg .start flag input [])).bind _ = _
    rw [start_delimit]
    change runSteps machine.step (a+(1+(b+(1+(accum.length+1))))) (outerEmbed (fun _ => []) (Turing.initList Outer input)) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+(b+(1+(accum.length+1)))) (outerEmbed (fun _ => []) outerEnd) = _
    rw [runSteps_add]
    change (machine.step (outerEmbed (fun _ => []) outerEnd)).bind _ = _
    rw [outer_done]
    change runSteps machine.step (b+(1+(accum.length+1))) (innerEmbed innerOther (Turing.initList Inner clause)) = _
    rw [runSteps_add,hbr]
    change runSteps machine.step (1+(accum.length+1)) (innerEmbed innerOther innerEnd) = _
    rw [runSteps_add]
    change (machine.step (innerEmbed innerOther innerEnd)).bind _ = _
    rw [inner_good]
    exact clear_run tail accum none

/-- An incomplete outer clause block reaches the failure continuation. -/
theorem bad_outer (input : List Bool) (flag : Option Bool) (hne : input ≠ [])
    (hbad : BitstringEncoding.undelimit input = none) :
    ∃ t ≤ input.length+3, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start flag input []) = some q ∧ q.l = some (.inl .bad) := by
  obtain ⟨n,hn,scratch,hr⟩ := Shared.ComplexityBridge.TM2Undelimit.invalid_run input [] [] none hbad
  rw [← Shared.ComplexityBridge.TM2Undelimit.initial_eq] at hr
  let finish := Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch []
  change runSteps Outer.step n (Turing.initList Outer input) = some finish at hr
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed (fun _ => [])) outerTerminal outer_stable (outer_step (fun _ => []))
    n (Turing.initList Outer input) finish (Or.inr rfl) hr
  obtain ⟨r,hs,hl⟩ := outer_rejected finish rfl
  refine ⟨1+a+1,by omega,r,?_,hl⟩
  cases input with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    rw [show 1+a+1 = 1+(a+1) by omega,runSteps_add]
    change (machine.step (cfg .start flag (x::xs) [])).bind _ = _
    rw [start_cons]
    change runSteps machine.step (a+1) (outerEmbed (fun _ => []) (Turing.initList Outer (x::xs))) = _
    rw [runSteps_add,har]
    exact hs

/-- A well-framed outer clause whose literal stream is malformed is rejected. -/
theorem bad_clause (clause tail : List Bool) (flag : Option Bool)
    (hbad : Shared.ComplexityBridge.TM2LiteralStream.parseNames clause = none) :
    ∃ t ≤ iterationPolynomial.eval (BitstringEncoding.delimit clause ++ tail).length, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start flag (BitstringEncoding.delimit clause ++ tail) []) = some q ∧ q.l = some (.inl .bad) := by
  let input := BitstringEncoding.delimit clause ++ tail
  let outerEnd := Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] clause
  let innerOther := stackVals tail [] [] [] [] [] []
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Inner
  let P := clause.length*(7*clause.length+11)+1
  have hp := Shared.ComplexityBridge.TM2Undelimit.valid_run clause tail
  change runSteps Outer.step (3*clause.length+2) (Turing.initList Outer input) = some outerEnd at hp
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed (fun _ => [])) outerTerminal outer_stable (outer_step (fun _ => []))
    _ (Turing.initList Outer input) outerEnd (Or.inl rfl) hp
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2LiteralStream.parse_progress clause
  have hq' : q.l = some (.inl .bad) := by simpa [hbad] using hq
  change n ≤ P at hn
  change runSteps Inner.step n (Turing.initList Inner clause) = some q at hr
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Inner.step machine.step (innerEmbed innerOther) innerTerminal inner_stable (inner_step innerOther)
    n (Turing.initList Inner clause) q (Or.inr hq') hr
  obtain ⟨r,hs,hl⟩ := inner_rejected q tail hq'
  have hin : clause.length ≤ input.length := by simp only [input,List.length_append,BitstringEncoding.length_delimit]; omega
  have hpoly := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono iterationPolynomial hin
  refine ⟨1+a+1+b+1,?_,r,?_,hl⟩
  · have hlocal : 1+a+1+b+1 ≤ iterationPolynomial.eval clause.length := by
      rw [iterationPolynomial_eval]
      change 1+a+1+b+1 ≤ (D+1)*P+4*clause.length+10
      rw [Nat.add_mul,Nat.one_mul]
      omega
    exact le_trans hlocal hpoly
  · rw [show 1+a+1+b+1 = 1+(a+(1+(b+1))) by omega,runSteps_add]
    change (machine.step (cfg .start flag input [])).bind _ = _
    rw [start_delimit]
    change runSteps machine.step (a+(1+(b+1))) (outerEmbed (fun _ => []) (Turing.initList Outer input)) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+(b+1)) (outerEmbed (fun _ => []) outerEnd) = _
    rw [runSteps_add]
    change (machine.step (outerEmbed (fun _ => []) outerEnd)).bind _ = _
    rw [outer_done]
    change runSteps machine.step (b+1) (innerEmbed innerOther (Turing.initList Inner clause)) = _
    rw [runSteps_add,hbr]
    exact hs

/-- Validate clauses separately, preserving the original outer boundaries. -/
def validate (input : List Bool) : Bool :=
  if input = [] then true else
    match h : BitstringEncoding.undelimit input with
    | none => false
    | some (clause,tail) =>
      if (Shared.ComplexityBridge.TM2LiteralStream.parseNames clause).isSome then validate tail else false
termination_by input.length
decreasing_by
  have hh := Shared.ComplexityBridge.CNFWitness.undelimit_sound input clause tail h
  have hl := congrArg List.length hh
  simp only [List.length_append,BitstringEncoding.length_delimit] at hl
  omega

theorem validate_nil : validate [] = true := by rw [validate]; rfl

theorem validate_bad_frame (x : Bool) (xs : List Bool) (h : BitstringEncoding.undelimit (x::xs) = none) :
    validate (x::xs) = false := by
  rw [validate]
  simp only [List.cons_ne_nil,if_false]
  split <;> simp_all

theorem validate_frame (clause tail : List Bool) :
    validate (BitstringEncoding.delimit clause ++ tail) =
      if (Shared.ComplexityBridge.TM2LiteralStream.parseNames clause).isSome then validate tail else false := by
  have hne : BitstringEncoding.delimit clause ++ tail ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_append,BitstringEncoding.length_delimit,List.length_nil] at hl
    omega
  rw [validate, if_neg hne, BitstringEncoding.undelimit_delimit]

theorem validate_framed (clauses : List (List Bool)) :
    validate (Shared.ComplexityBridge.TM2WitnessLookup.frames clauses) =
      clauses.all (fun c => (Shared.ComplexityBridge.TM2LiteralStream.parseNames c).isSome) := by
  induction clauses with
  | nil => simpa [Shared.ComplexityBridge.TM2WitnessLookup.frames] using validate_nil
  | cons c clauses ih =>
    rw [Shared.ComplexityBridge.TM2WitnessLookup.frames_cons,validate_frame]
    cases hc : Shared.ComplexityBridge.TM2LiteralStream.parseNames c <;> simp [hc,ih]

/-- Malformed outer framing is rejected independently of clause contents. -/
theorem validate_bad_blocks (input : List Bool) (hbad : BitstringEncoding.undelimitBlocks input = none) : validate input = false := by
  cases input with
  | nil => simp [BitstringEncoding.undelimitBlocks,BitstringEncoding.undelimitBlocksAux] at hbad
  | cons x xs =>
    cases ho : BitstringEncoding.undelimit (x::xs) with
    | none => exact validate_bad_frame x xs ho
    | some p =>
      rcases p with ⟨clause,tail⟩
      have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound (x::xs) clause tail ho
      have htail : BitstringEncoding.undelimitBlocks tail = none := by
        cases ht : BitstringEncoding.undelimitBlocks tail with
        | none => rfl
        | some blocks =>
          have hblocks := Shared.ComplexityBridge.CNFWitness.blocks_sound tail blocks ht
          have hfull : Shared.ComplexityBridge.TM2WitnessLookup.frames (clause::blocks) = x::xs := by
            rw [Shared.ComplexityBridge.TM2WitnessLookup.frames_cons]
            change BitstringEncoding.delimit clause ++ (blocks.map BitstringEncoding.delimit).flatten = x::xs
            rw [hblocks]; exact he
          have hv := BitstringEncoding.undelimitBlocks_flatten_delimit (clause::blocks)
          change BitstringEncoding.undelimitBlocks (Shared.ComplexityBridge.TM2WitnessLookup.frames (clause::blocks)) = _ at hv
          rw [hfull,hbad] at hv
          contradiction
      have hlt : tail.length < (x::xs).length := by
        have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit,List.length_cons] at hl
        simp only [List.length_cons]; omega
      rw [← he,validate_frame]
      cases hn : Shared.ComplexityBridge.TM2LiteralStream.parseNames clause with
      | none => rfl
      | some names => simpa [hn] using validate_bad_blocks tail htail
termination_by input.length

/-- Exact all-bitstrings agreement with the public CNF parser's success test. -/
theorem validate_correct (input : List Bool) : validate input = (Shared.ComplexityBridge.CNF.parse input).isSome := by
  change validate input = ((BitstringEncoding.undelimitBlocks input).bind
    (List.mapM (BitstringEncoding.bitDecode (α := Shared.ComplexityBridge.CNF.Clause)))).isSome
  cases h : BitstringEncoding.undelimitBlocks input with
  | none => simpa [h] using validate_bad_blocks input h
  | some clauses =>
    have he := Shared.ComplexityBridge.CNFWitness.blocks_sound input clauses h
    change Shared.ComplexityBridge.TM2WitnessLookup.frames clauses = input at he
    rw [← he,validate_framed]
    have hh : BitstringEncoding.undelimitBlocks (Shared.ComplexityBridge.TM2WitnessLookup.frames clauses) = some clauses := by simpa [he] using h
    simp only [Option.bind_some,mapM_isSome]
    congr 1; funext c; exact clause_defined c

/-- Every clause comparison finishes; the entire validation run reaches its
correct continuation within a polynomial bound, even on malformed inputs. -/
theorem validation_run (input : List Bool) (flag : Option Bool) :
    ∃ t ≤ input.length * iterationPolynomial.eval input.length + 1, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start flag input []) = some q ∧
        q.l = some (.inl (if validate input then .good else .bad)) := by
  cases input with
  | nil =>
    refine ⟨1,by simp, cfg .good none [] [], start_nil flag, ?_⟩
    simp [validate_nil,cfg]
  | cons x xs =>
    let input := x::xs
    change ∃ t ≤ input.length * iterationPolynomial.eval input.length + 1, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start flag input []) = some q ∧
        q.l = some (.inl (if validate input then .good else .bad))
    have hpos : 1 ≤ input.length := by simp [input]
    have hK : 4 ≤ iterationPolynomial.eval input.length := by rw [iterationPolynomial_eval]; omega
    have hmul := Nat.mul_le_mul_left input.length hK
    cases ho : BitstringEncoding.undelimit input with
    | none =>
      obtain ⟨t,ht,q,hr,hq⟩ := bad_outer input flag (by simp [input]) ho
      refine ⟨t,by omega,q,hr,?_⟩
      have hv : validate input = false := validate_bad_frame x xs ho
      simpa [hv] using hq
    | some pair =>
      rcases pair with ⟨clause,tail⟩
      have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound input clause tail ho
      have hlt : tail.length < input.length := by
        have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit] at hl
        omega
      cases hn : Shared.ComplexityBridge.TM2LiteralStream.parseNames clause with
      | none =>
        obtain ⟨t,ht,q,hr,hq⟩ := bad_clause clause tail flag hn
        have hbound : iterationPolynomial.eval input.length ≤ input.length * iterationPolynomial.eval input.length := by
          have hh := Nat.mul_le_mul_right (iterationPolynomial.eval input.length) hpos
          simpa using hh
        refine ⟨t,?_,q,?_,?_⟩
        · rw [he] at ht; omega
        · simpa [he] using hr
        · have hv : validate input = false := by rw [← he,validate_frame,hn]; rfl
          simpa [hv] using hq
      | some names =>
        obtain ⟨a,ha,har⟩ := process_one clause tail flag names hn
        obtain ⟨b,hb,q,hbr,hq⟩ := validation_run tail none
        have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono iterationPolynomial (Nat.le_of_lt hlt)
        have hmb := Nat.mul_le_mul_left tail.length hm
        have htail := Nat.mul_le_mul_right (iterationPolynomial.eval input.length) (show tail.length+1 ≤ input.length by omega)
        have hbound : a+b ≤ input.length * iterationPolynomial.eval input.length+1 := by
          rw [he] at ha
          rw [Nat.add_mul,Nat.one_mul] at htail
          omega
        refine ⟨a+b,hbound,q,?_,?_⟩
        · rw [← he,runSteps_add,har]; exact hbr
        · have hv : validate input = validate tail := by rw [← he,validate_frame,hn]; rfl
          simpa [hv] using hq
termination_by input.length

end Shared.ComplexityBridge.TM2CNFValidate
