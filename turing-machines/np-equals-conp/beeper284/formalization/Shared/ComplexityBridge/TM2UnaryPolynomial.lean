import Shared.ComplexityBridge.TM2UnaryMonomial
import Shared.Codes.NumericPolynomial

namespace Shared.ComplexityBridge.TM2UnaryPolynomial
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Terms := Shared.Codes.NumericPolynomial.Terms
abbrev Key := Shared.ComplexityBridge.TM2UnaryMonomial.Key
abbrev Mono := Shared.ComplexityBridge.TM2UnaryMonomial.machine

def Label : Terms → Type
  | [] => Unit
  | (c,e)::ts => Shared.ComplexityBridge.TM2UnaryMonomial.Label e c ⊕ (Unit ⊕ Label ts)

instance labelFintype : ∀ ts : Terms, Fintype (Label ts)
  | [] => inferInstanceAs (Fintype Unit)
  | (c,e)::ts => by
    letI := labelFintype ts
    change Fintype (Shared.ComplexityBridge.TM2UnaryMonomial.Label e c ⊕ (Unit ⊕ Label ts))
    exact inferInstance

instance labelDecidableEq : ∀ ts : Terms, DecidableEq (Label ts)
  | [] => inferInstanceAs (DecidableEq Unit)
  | (c,e)::ts => by
    letI := labelDecidableEq ts
    change DecidableEq (Shared.ComplexityBridge.TM2UnaryMonomial.Label e c ⊕ (Unit ⊕ Label ts))
    exact inferInstance

def startLabel : (ts : Terms) → Label ts
  | [] => ()
  | (c,e)::_ => .inl (Mono e c).main

def doneLabel : (ts : Terms) → Label ts
  | [] => ()
  | _::ts => .inr (.inr (doneLabel ts))

def retag {L L' : Type} (f : L → L') : Stmt (fun _ : Key => Bool) L Bool →
    Stmt (fun _ : Key => Bool) L' Bool
  | .push j g q => .push j g (retag f q)
  | .peek j g q => .peek j g (retag f q)
  | .pop j g q => .pop j g (retag f q)
  | .load g q => .load g (retag f q)
  | .branch g q r => .branch g (retag f q) (retag f r)
  | .goto g => .goto (f ∘ g)
  | .halt => .halt

def embed {L L' : Type} (f : L → L') (q : Cfg (fun _ : Key => Bool) L Bool) : Cfg (fun _ : Key => Bool) L' Bool :=
  ⟨q.l.map f,q.var,q.stk⟩

theorem retag_aux {L L' : Type} (f : L → L') (q : Stmt (fun _ : Key => Bool) L Bool)
    (v : Bool) (S : Key → List Bool) : stepAux (retag f q) v S = embed f (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto g => rfl
  | load g q ih => exact ih (g v) S
  | push j g q ih => exact ih v _
  | peek j g q ih => exact ih _ S
  | pop j g q ih => exact ih _ _
  | branch g q r ihq ihr => by_cases h : g v <;> simp [retag,stepAux,h,ihq,ihr]

def program : (ts : Terms) → Label ts → Stmt (fun _ : Key => Bool) (Label ts) Bool
  | [], () => .goto (fun _ => ())
  | (c,e)::ts, .inl l =>
      if l = Shared.ComplexityBridge.TM2UnaryMonomial.endLabel e c then .goto (fun _ => .inr (.inl ()))
      else retag Sum.inl (Shared.ComplexityBridge.TM2UnaryMonomial.program e c l)
  | (c,e)::ts, .inr (.inl ()) =>
      .pop (.inr .a) (fun _ h => h.isSome)
        (.branch id (.goto (fun _ => .inr (.inl ())))
          (.push (.inr .a) (fun _ => true) (.goto (fun _ => .inr (.inr (startLabel ts))))))
  | (c,e)::ts, .inr (.inr l) => retag (fun q => .inr (.inr q)) (program ts l)

def machine (ts : Terms) : Turing.FinTM2 where
  K := Key
  k₀ := .inr .a
  k₁ := .inl true
  Γ := fun _ => Bool
  Λ := Label ts
  main := startLabel ts
  σ := Bool
  initialState := false
  m := program ts

def stackVals (n a out : Nat) : Key → List Bool :=
  Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks [] (List.replicate out true)
    (Shared.ComplexityBridge.TM2UnaryMultiply.stackVals a n 0 0 0)

def initialCfg (ts : Terms) (n out : Nat) : (machine ts).Cfg :=
  ⟨some (startLabel ts),false,stackVals n 1 out⟩

def finalCfg (ts : Terms) (n out : Nat) : (machine ts).Cfg :=
  ⟨some (doneLabel ts),false,stackVals n 1 out⟩

def monoEmbed (c e : Nat) (ts : Terms) (q : (Mono e c).Cfg) : (machine ((c,e)::ts)).Cfg :=
  embed Sum.inl q

def tailEmbed (c e : Nat) (ts : Terms) (q : (machine ts).Cfg) : (machine ((c,e)::ts)).Cfg :=
  embed (fun l => .inr (.inr l)) q

set_option backward.isDefEq.respectTransparency false in
theorem mono_step (c e : Nat) (ts : Terms) (q : (Mono e c).Cfg)
    (h : ¬ Shared.ComplexityBridge.TM2UnaryMonomial.endTerminal e c q) :
    (machine ((c,e)::ts)).step (monoEmbed c e ts q) = ((Mono e c).step q).map (monoEmbed c e ts) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      have hl : l ≠ Shared.ComplexityBridge.TM2UnaryMonomial.endLabel e c := by intro he; apply h; exact congrArg some he
      change some (stepAux (program ((c,e)::ts) (.inl l)) v S) = _
      simp only [program,if_neg hl]
      rw [retag_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem tail_step (c e : Nat) (ts : Terms) (q : (machine ts).Cfg) :
    (machine ((c,e)::ts)).step (tailEmbed c e ts q) = ((machine ts).step q).map (tailEmbed c e ts) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (retag (fun q => (Sum.inr (Sum.inr q) : Label ((c,e)::ts))) (program ts l)) v S) = _
      rw [retag_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem tail_run (c e : Nat) (ts : Terms) (q : (machine ts).Cfg) (n : Nat) :
    runSteps (machine ((c,e)::ts)).step n (tailEmbed c e ts q) =
      (runSteps (machine ts).step n q).map (tailEmbed c e ts) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,tail_step]
    cases h : (machine ts).step q with
    | none => rfl
    | some q' => exact ih q'

def resetCfg (c e : Nat) (ts : Terms) (flag : Bool) (n a out : Nat) : (machine ((c,e)::ts)).Cfg :=
  ⟨some (.inr (.inl ())),flag,stackVals n a out⟩

theorem reset_cons (c e : Nat) (ts : Terms) (flag : Bool) (n a out : Nat) :
    (machine ((c,e)::ts)).step (resetCfg c e ts flag n (a+1) out) =
      some (resetCfg c e ts true n a out) := by
  change some (Cfg.mk (some (.inr (.inl ()) : Label ((c,e)::ts))) true
    (Function.update (stackVals n (a+1) out) (.inr .a) (List.replicate a true))) = _
  congr 1; congr 1; funext j
  cases j with
  | inl b => cases b <;> simp [stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
      Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Function.update]
  | inr q => cases q <;> simp [stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
      Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Function.update]

theorem reset_nil (c e : Nat) (ts : Terms) (flag : Bool) (n out : Nat) :
    (machine ((c,e)::ts)).step (resetCfg c e ts flag n 0 out) =
      some (tailEmbed c e ts (initialCfg ts n out)) := by
  change some (Cfg.mk (some (.inr (.inr (startLabel ts)) : Label ((c,e)::ts))) false
    (Function.update (Function.update (stackVals n 0 out) (.inr .a) []) (.inr .a) [true])) = _
  congr 1; congr 1; funext j
  cases j with
  | inl b => cases b <;> simp [initialCfg,tailEmbed,embed,stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
      Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Function.update]
  | inr q => cases q <;> simp [initialCfg,tailEmbed,embed,stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
      Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Function.update]

theorem reset_run (c e : Nat) (ts : Terms) (a : Nat) (flag : Bool) (n out : Nat) :
    runSteps (machine ((c,e)::ts)).step (a+1) (resetCfg c e ts flag n a out) =
      some (tailEmbed c e ts (initialCfg ts n out)) := by
  induction a generalizing flag with
  | zero =>
    change (machine ((c,e)::ts)).step (resetCfg c e ts flag n 0 out) = _
    exact reset_nil c e ts flag n out
  | succ a ih =>
    rw [show a+1+1 = (a+1)+1 by omega,runSteps_front,reset_cons]
    exact ih true

/-- The monomial's stable continuation transfers to the resetting routine in
one charged block. -/
theorem mono_dispatch (c e : Nat) (ts : Terms) (n out : Nat) :
    (machine ((c,e)::ts)).step (monoEmbed c e ts (Shared.ComplexityBridge.TM2UnaryMonomial.scaleEmbed e c
      (Shared.ComplexityBridge.TM2UnaryMonomial.otherStacks n)
      (Shared.ComplexityBridge.TM2UnaryScale.cfg (Shared.ComplexityBridge.TM2UnaryScale.index c c (by omega))
        false false (n^e) 0 (out+c*(n^e))))) =
      some (resetCfg c e ts false n (n^e) (out+c*(n^e))) := by
  change some (stepAux (program ((c,e)::ts) (.inl (Shared.ComplexityBridge.TM2UnaryMonomial.endLabel e c))) false
    (Shared.ComplexityBridge.TM2UnaryMonomial.scaleStacks
      (Shared.ComplexityBridge.TM2UnaryScale.stackVals (n^e) 0 (out+c*(n^e)))
      (Shared.ComplexityBridge.TM2UnaryMonomial.otherStacks n))) = _
  simp only [program,ite_true,stepAux]
  congr 1; congr 1; funext j
  cases j with
  | inl b => cases b <;> simp [stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.scaleStacks,
      Shared.ComplexityBridge.TM2UnaryMonomial.otherStacks,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
      Shared.ComplexityBridge.TM2UnaryScale.stackVals,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]
  | inr q => cases q <;> simp [stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.scaleStacks,
      Shared.ComplexityBridge.TM2UnaryMonomial.otherStacks,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
      Shared.ComplexityBridge.TM2UnaryScale.stackVals,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]

/-- Sum of fixed monomial, dispatch, reset and recursive-tail costs. -/
def cost : Terms → Nat → Nat
  | [], _ => 0
  | (c,e)::ts, n => (e*14*(n+2)^e + 1 + c*(2*(n^e)+2)) + 1 + (n^e+1) + cost ts n

set_option backward.isDefEq.respectTransparency false in
/-- A fixed finite term list is compiled into finite control. Starting with a
unary base and accumulator, it adds the exact natural polynomial value,
preserves the base, restores the unit operand, and reaches a continuation. -/
theorem evaluate (ts : Terms) (n out : Nat) :
    ∃ t ≤ cost ts n,
      runSteps (machine ts).step t (initialCfg ts n out) =
        some (finalCfg ts n (out+Shared.Codes.NumericPolynomial.eval ts n)) := by
  induction ts generalizing out with
  | nil => exact ⟨0,by simp [cost],by simp [initialCfg,finalCfg,startLabel,doneLabel,Shared.Codes.NumericPolynomial.eval,runSteps]⟩
  | cons term ts ih =>
    rcases term with ⟨c,e⟩
    obtain ⟨m,hm,hmono⟩ := Shared.ComplexityBridge.TM2UnaryMonomial.monomial e c n out
    let qstart := Shared.ComplexityBridge.TM2UnaryMonomial.powerEmbed e c [] (List.replicate out true)
      (Shared.ComplexityBridge.TM2UnaryMonomial.powerStart e n)
    let qend := Shared.ComplexityBridge.TM2UnaryMonomial.scaleEmbed e c
      (Shared.ComplexityBridge.TM2UnaryMonomial.otherStacks n)
      (Shared.ComplexityBridge.TM2UnaryScale.cfg (Shared.ComplexityBridge.TM2UnaryScale.index c c (by omega))
        false false (n^e) 0 (out+c*(n^e)))
    letI : DecidablePred (Shared.ComplexityBridge.TM2UnaryMonomial.endTerminal e c) := fun _ => Classical.propDecidable _
    obtain ⟨a,ha,haRun⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      (Mono e c).step (machine ((c,e)::ts)).step (monoEmbed c e ts)
      (Shared.ComplexityBridge.TM2UnaryMonomial.endTerminal e c)
      (Shared.ComplexityBridge.TM2UnaryMonomial.end_stable e c) (mono_step c e ts) m qstart qend (by rfl) hmono
    obtain ⟨t,ht,htail⟩ := ih (out+c*(n^e))
    have htail' := tail_run c e ts (initialCfg ts n (out+c*(n^e))) t
    rw [htail] at htail'
    change runSteps (machine ((c,e)::ts)).step t (tailEmbed c e ts (initialCfg ts n (out+c*(n^e)))) =
      some (tailEmbed c e ts (finalCfg ts n ((out+c*(n^e))+Shared.Codes.NumericPolynomial.eval ts n))) at htail'
    have hf : tailEmbed c e ts (finalCfg ts n ((out+c*(n^e))+Shared.Codes.NumericPolynomial.eval ts n)) =
        finalCfg ((c,e)::ts) n (out+Shared.Codes.NumericPolynomial.eval ((c,e)::ts) n) := by
      simp [tailEmbed,embed,finalCfg,doneLabel,Shared.Codes.NumericPolynomial.eval,Nat.add_assoc]
    rw [hf] at htail'
    refine ⟨a+1+(n^e+1)+t,?_ ,?_⟩
    · simp only [cost]
      omega
    · have hin : initialCfg ((c,e)::ts) n out = monoEmbed c e ts qstart := by rfl
      rw [hin]
      have hn : a+1+(n^e+1)+t = a+((n^e+1+t)+1) := by omega
      rw [hn,runSteps_add,haRun]
      change runSteps (machine ((c,e)::ts)).step ((n^e+1+t)+1) (monoEmbed c e ts qend) = _
      rw [runSteps_front,mono_dispatch]
      change runSteps (machine ((c,e)::ts)).step ((n^e+1)+t) (resetCfg c e ts false n (n^e) (out+c*(n^e))) = _
      rw [runSteps_add,reset_run]
      exact htail'

/-- An explicit polynomial evaluates to the exact uniform cost expression. -/
noncomputable def costPolynomial : Terms → Polynomial Nat
  | [] => 0
  | (c,e)::ts =>
      Polynomial.C (e*14)*(Polynomial.X+Polynomial.C 2)^e + Polynomial.C 1 +
        Polynomial.C c*(Polynomial.C 2*Polynomial.X^e+Polynomial.C 2) + Polynomial.C 1 +
        (Polynomial.X^e+Polynomial.C 1) + costPolynomial ts

theorem costPolynomial_eval (ts : Terms) (n : Nat) : (costPolynomial ts).eval n = cost ts n := by
  induction ts with
  | nil => simp [costPolynomial,cost]
  | cons term ts ih =>
    rcases term with ⟨c,e⟩
    simp [costPolynomial,cost,ih]

/-- The final label self-loops on every state and stack configuration, so a
later finite machine can replace that continuation by a charged dispatch. -/
theorem done_aux (ts : Terms) (v : Bool) (S : Key → List Bool) :
    stepAux (program ts (doneLabel ts)) v S = ⟨some (doneLabel ts),v,S⟩ := by
  induction ts with
  | nil => rfl
  | cons term ts ih =>
    rcases term with ⟨c,e⟩
    change stepAux (retag (fun q => (Sum.inr (Sum.inr q) : Label ((c,e)::ts))) (program ts (doneLabel ts))) v S = _
    rw [retag_aux,ih]
    rfl

def doneTerminal (ts : Terms) (q : (machine ts).Cfg) : Prop := q.l = some (doneLabel ts)
noncomputable instance (ts : Terms) : DecidablePred (doneTerminal ts) := fun _ => Classical.propDecidable _

set_option backward.isDefEq.respectTransparency false in
theorem done_stable (ts : Terms) (q : (machine ts).Cfg) (h : doneTerminal ts q) : (machine ts).step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (doneLabel ts) at h
    subst l
    change some (stepAux (program ts (doneLabel ts)) v S) = _
    rw [done_aux]

/-- The compiled finite machine evaluates `3n² + 4` at `n = 2`. -/
example : (runSteps (machine [(3,2),(4,0)]).step 102 (initialCfg [(3,2),(4,0)] 2 0)).map
    (fun q => q.stk (.inl true)) = some (List.replicate 16 true) := by
  change (Option.map (fun q => q.stk (.inl true))
    (runSteps (machine [(3,2),(4,0)]).step 102 (initialCfg [(3,2),(4,0)] 2 0)) : Option (List Bool)) = _
  decide

/-- The empty term list preserves the initial accumulator without a step. -/
example : (runSteps (machine []).step 0 (initialCfg [] 0 2)).map
    (fun q => q.stk (.inl true)) = some [true,true] := by
  change (Option.map (fun q => q.stk (.inl true)) (runSteps (machine []).step 0 (initialCfg [] 0 2)) : Option (List Bool)) = _
  decide

end Shared.ComplexityBridge.TM2UnaryPolynomial
