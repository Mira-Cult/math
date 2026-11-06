import Shared.ComplexityBridge.TM2UnaryScale

namespace Shared.ComplexityBridge.TM2UnaryMonomial
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev PStack := Shared.ComplexityBridge.TM2UnaryMultiply.Stack
abbrev SStack := Shared.ComplexityBridge.TM2UnaryScale.Stack
abbrev Power := Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.machine
abbrev Scale := Shared.ComplexityBridge.TM2UnaryScale.machine
abbrev Key := Bool ⊕ PStack
abbrev Label (e c : Nat) := Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.Labels e ⊕
  Shared.ComplexityBridge.TM2UnaryScale.Label c

def powerStacks (scratch output : List Bool) (S : PStack → List Bool) : Key → List Bool
  | .inl false => scratch
  | .inl true => output
  | .inr j => S j

theorem power_update (scratch output : List Bool) (S : PStack → List Bool) (j : PStack) (xs : List Bool) :
    powerStacks scratch output (Function.update S j xs) = Function.update (powerStacks scratch output S) (.inr j) xs := by
  funext q
  cases q with
  | inl b => cases b <;> simp [powerStacks,Function.update]
  | inr q =>
    by_cases h : q = j
    · subst q; simp [powerStacks,Function.update]
    · have hh : (Sum.inr q : Key) ≠ .inr j := by simpa using h
      simp [powerStacks,Function.update_of_ne h,Function.update_of_ne hh]

def scaleKey : SStack → Key
  | .operand => .inr .a
  | .scratch => .inl false
  | .output => .inl true

def scaleStacks (S : SStack → List Bool) (other : PStack → List Bool) : Key → List Bool
  | .inl false => S .scratch
  | .inl true => S .output
  | .inr .a => S .operand
  | .inr j => other j

@[simp] theorem scaleStacks_apply (S : SStack → List Bool) (other : PStack → List Bool) (j : SStack) :
    scaleStacks S other (scaleKey j) = S j := by cases j <;> rfl

theorem scale_update (S : SStack → List Bool) (other : PStack → List Bool) (j : SStack) (xs : List Bool) :
    scaleStacks (Function.update S j xs) other = Function.update (scaleStacks S other) (scaleKey j) xs := by
  funext q
  cases j <;> cases q with
  | inl b => cases b <;> simp [scaleStacks,scaleKey,Function.update]
  | inr q => cases q <;> simp [scaleStacks,scaleKey,Function.update]

def liftPower (e c : Nat) : Stmt (fun _ : PStack => Bool) (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.Labels e) Bool →
    Stmt (fun _ : Key => Bool) (Label e c) Bool
  | .push j f q => .push (.inr j) f (liftPower e c q)
  | .peek j f q => .peek (.inr j) f (liftPower e c q)
  | .pop j f q => .pop (.inr j) f (liftPower e c q)
  | .load f q => .load f (liftPower e c q)
  | .branch f q r => .branch f (liftPower e c q) (liftPower e c r)
  | .goto f => .goto (fun s => .inl (f s))
  | .halt => .halt

def liftScale (e c : Nat) : Stmt (fun _ : SStack => Bool) (Shared.ComplexityBridge.TM2UnaryScale.Label c) Bool →
    Stmt (fun _ : Key => Bool) (Label e c) Bool
  | .push j f q => .push (scaleKey j) f (liftScale e c q)
  | .peek j f q => .peek (scaleKey j) f (liftScale e c q)
  | .pop j f q => .pop (scaleKey j) f (liftScale e c q)
  | .load f q => .load f (liftScale e c q)
  | .branch f q r => .branch f (liftScale e c q) (liftScale e c r)
  | .goto f => .goto (fun s => .inr (f s))
  | .halt => .halt

def powerEmbed (e c : Nat) (scratch output : List Bool) (q : (Power e).Cfg) :
    Cfg (fun _ : Key => Bool) (Label e c) Bool := ⟨q.l.map Sum.inl,q.var,powerStacks scratch output q.stk⟩

def scaleEmbed (e c : Nat) (other : PStack → List Bool) (q : (Scale c).Cfg) :
    Cfg (fun _ : Key => Bool) (Label e c) Bool := ⟨q.l.map Sum.inr,q.var,scaleStacks q.stk other⟩

theorem liftPower_aux (e c : Nat)
    (q : Stmt (fun _ : PStack => Bool) (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.Labels e) Bool)
    (v : Bool) (S : PStack → List Bool) (scratch output : List Bool) :
    stepAux (liftPower e c q) v (powerStacks scratch output S) = powerEmbed e c scratch output (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push j f q ih =>
    simp only [liftPower,stepAux,powerStacks]
    rw [← power_update scratch output S j (f v::S j)]
    exact ih v _
  | peek j f q ih => exact ih (f v (S j).head?) S
  | pop j f q ih =>
    simp only [liftPower,stepAux,powerStacks]
    rw [← power_update scratch output S j (S j).tail]
    exact ih (f v (S j).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftPower,stepAux,h,ihq,ihr]

set_option backward.isDefEq.respectTransparency false in
theorem liftScale_aux (e c : Nat)
    (q : Stmt (fun _ : SStack => Bool) (Shared.ComplexityBridge.TM2UnaryScale.Label c) Bool)
    (v : Bool) (S : SStack → List Bool) (other : PStack → List Bool) :
    stepAux (liftScale e c q) v (scaleStacks S other) = scaleEmbed e c other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push j f q ih =>
    simp only [liftScale,stepAux,scaleStacks_apply]
    rw [← scale_update S other j (f v::S j)]
    exact ih v _
  | peek j f q ih =>
    simp only [liftScale,stepAux,scaleStacks_apply]
    exact ih (f v (S j).head?) S
  | pop j f q ih =>
    simp only [liftScale,stepAux,scaleStacks_apply]
    rw [← scale_update S other j (S j).tail]
    exact ih (f v (S j).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftScale,stepAux,h,ihq,ihr]

def powerEnd (e : Nat) : Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.Labels e :=
  (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index e e (by omega), .inl .outer)

def program (e c : Nat) : Label e c → Stmt (fun _ : Key => Bool) (Label e c) Bool
  | .inl l => if l = powerEnd e then .goto (fun _ => .inr (Shared.ComplexityBridge.TM2UnaryScale.index c 0 (by omega),false))
      else liftPower e c (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.program e l)
  | .inr l => liftScale e c (Shared.ComplexityBridge.TM2UnaryScale.program c l)

def machine (e c : Nat) : Turing.FinTM2 where
  K := Key
  k₀ := .inr .a
  k₁ := .inl true
  Γ := fun _ => Bool
  Λ := Label e c
  main := .inl (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index e 0 (by omega), .inl .outer)
  σ := Bool
  initialState := false
  m := program e c

def powerTerminal (e : Nat) (q : (Power e).Cfg) : Prop := q.l = some (powerEnd e)
noncomputable instance (e : Nat) : DecidablePred (powerTerminal e) := fun _ => Classical.propDecidable _

theorem power_stable (e : Nat) (q : (Power e).Cfg) (h : powerTerminal e q) : (Power e).step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (powerEnd e) at h
    subst l
    change some (stepAux (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.program e (powerEnd e)) v S) = _
    simp [Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.program,
      Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index,powerEnd,stepAux]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem power_step (e c : Nat) (scratch output : List Bool) (q : (Power e).Cfg) (h : ¬ powerTerminal e q) :
    (machine e c).step (powerEmbed e c scratch output q) = ((Power e).step q).map (powerEmbed e c scratch output) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      have hl : l ≠ powerEnd e := by intro he; apply h; exact congrArg some he
      change some (stepAux (program e c (.inl l)) v (powerStacks scratch output S)) = _
      simp only [program,if_neg hl]
      rw [liftPower_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem scale_step (e c : Nat) (other : PStack → List Bool) (q : (Scale c).Cfg) :
    (machine e c).step (scaleEmbed e c other q) = ((Scale c).step q).map (scaleEmbed e c other) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftScale e c (Shared.ComplexityBridge.TM2UnaryScale.program c l)) v (scaleStacks S other)) = _
      rw [liftScale_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem scale_run (e c : Nat) (other : PStack → List Bool) (q : (Scale c).Cfg) (n : Nat) :
    runSteps (machine e c).step n (scaleEmbed e c other q) =
      (runSteps (Scale c).step n q).map (scaleEmbed e c other) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,scale_step]
    cases h : (Scale c).step q with
    | none => rfl
    | some q' => exact ih q'

def powerStart (e n : Nat) : (Power e).Cfg :=
  Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.mulEmbed
    (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index e 0 (by omega))
    (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 n 0 0 0)

def powerFinished (e n : Nat) : (Power e).Cfg :=
  Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.mulEmbed
    (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index e e (by omega))
    (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false (n^e) n 0 0 0)

def otherStacks (n : Nat) : PStack → List Bool := Shared.ComplexityBridge.TM2UnaryMultiply.stackVals 0 n 0 0 0

theorem dispatch (e c n out : Nat) :
    (machine e c).step (powerEmbed e c [] (List.replicate out true) (powerFinished e n)) =
      some (scaleEmbed e c (otherStacks n)
        (Shared.ComplexityBridge.TM2UnaryScale.cfg (Shared.ComplexityBridge.TM2UnaryScale.index c 0 (by omega)) false false (n^e) 0 out)) := by
  change some (stepAux (program e c (.inl (powerEnd e))) false
    (powerStacks [] (List.replicate out true) (Shared.ComplexityBridge.TM2UnaryMultiply.stackVals (n^e) n 0 0 0))) = _
  simp only [program,ite_true,stepAux]
  congr 1
  congr 1
  funext j
  cases j with
  | inl b => cases b <;> simp [scaleEmbed,scaleStacks,otherStacks,powerStacks,
      Shared.ComplexityBridge.TM2UnaryScale.cfg,Shared.ComplexityBridge.TM2UnaryScale.stackVals]
  | inr q => cases q <;> simp [scaleEmbed,scaleStacks,otherStacks,powerStacks,
      Shared.ComplexityBridge.TM2UnaryScale.cfg,Shared.ComplexityBridge.TM2UnaryScale.stackVals,
      Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]

set_option backward.isDefEq.respectTransparency false in
/-- Fixed finite control computes and appends `c*n^e` unary ticks. The base
operand and accumulated output are explicitly supplied; both dispatch and all
copy blocks are charged. -/
theorem monomial (e c n out : Nat) :
    ∃ t ≤ e*14*(n+2)^e + 1 + c*(2*(n^e)+2),
      runSteps (machine e c).step t (powerEmbed e c [] (List.replicate out true) (powerStart e n)) =
      some (scaleEmbed e c (otherStacks n)
        (Shared.ComplexityBridge.TM2UnaryScale.cfg (Shared.ComplexityBridge.TM2UnaryScale.index c c (by omega))
          false false (n^e) 0 (out+c*(n^e)))) := by
  obtain ⟨m,hm,hpower⟩ := Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.fixed_power e n
  have hpower' : runSteps (Power e).step m (powerStart e n) = some (powerFinished e n) := by
    simpa [powerStart,powerFinished,Nat.mul_comm] using hpower
  letI : DecidablePred (powerTerminal e) := fun _ => Classical.propDecidable _
  obtain ⟨a,ha,hr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Power e).step (machine e c).step (powerEmbed e c [] (List.replicate out true))
    (powerTerminal e) (power_stable e) (power_step e c [] (List.replicate out true)) m
    (powerStart e n) (powerFinished e n) (by rfl) hpower'
  have hscale := Shared.ComplexityBridge.TM2UnaryScale.scale c (n^e) out
  have hs := scale_run e c (otherStacks n)
    (Shared.ComplexityBridge.TM2UnaryScale.cfg (Shared.ComplexityBridge.TM2UnaryScale.index c 0 (by omega)) false false (n^e) 0 out)
    (c*(2*(n^e)+2))
  rw [hscale] at hs
  refine ⟨a+1+c*(2*(n^e)+2),by omega,?_⟩
  have ht : a+1+c*(2*(n^e)+2) = a+(c*(2*(n^e)+2)+1) := by omega
  rw [ht,runSteps_add,hr]
  change runSteps (machine e c).step (c*(2*(n^e)+2)+1)
    (powerEmbed e c [] (List.replicate out true) (powerFinished e n)) = _
  rw [runSteps_front,dispatch]
  exact hs

/-- The completed monomial has a stable label suitable for a charged
continuation to the next polynomial term. -/
def endLabel (e c : Nat) : Label e c :=
  .inr (Shared.ComplexityBridge.TM2UnaryScale.index c c (by omega),false)

def endTerminal (e c : Nat) (q : (machine e c).Cfg) : Prop := q.l = some (endLabel e c)
noncomputable instance (e c : Nat) : DecidablePred (endTerminal e c) := fun _ => Classical.propDecidable _

theorem end_stable (e c : Nat) (q : (machine e c).Cfg) (h : endTerminal e c q) :
    (machine e c).step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (endLabel e c) at h
    subst l
    change some (stepAux (program e c (endLabel e c)) v S) = _
    simp [program,endLabel,Shared.ComplexityBridge.TM2UnaryScale.program,
      Shared.ComplexityBridge.TM2UnaryScale.index,liftScale,stepAux]
    rfl

/-- Two squared, scaled by three and appended to one existing tick. -/
example : (runSteps (machine 2 3).step 76
    (powerEmbed 2 3 [] [true] (powerStart 2 2))).map (fun q => q.stk (.inl true)) =
      some (List.replicate 13 true) := by
  change (Option.map (fun q => q.stk (.inl true)) (runSteps (machine 2 3).step 76
    (powerEmbed 2 3 [] [true] (powerStart 2 2))) : Option (List Bool)) = _
  decide

/-- A zero coefficient does not alter the existing accumulator. -/
example : (runSteps (machine 0 0).step 1
    (powerEmbed 0 0 [] [true,true] (powerStart 0 0))).map (fun q => q.stk (.inl true)) = some [true,true] := by
  change (Option.map (fun q => q.stk (.inl true)) (runSteps (machine 0 0).step 1
    (powerEmbed 0 0 [] [true,true] (powerStart 0 0))) : Option (List Bool)) = _
  decide

end Shared.ComplexityBridge.TM2UnaryMonomial
