import Shared.ComplexityBridge.TM2StrictCleanup

namespace Shared.ComplexityBridge.TM2AuxSweep
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2PairClock Shared.ComplexityBridge.TM2FiniteReverse
abbrev PStack := Shared.ComplexityBridge.TM2UnaryMultiply.Stack
abbrev Index := Fin 5
abbrev Phase := Fin 6
abbrev AuxState (states : Nat) := Bool × Fin (states+1) × Bool

def stackIndex : PStack → Index
  | .a => ⟨0,by decide⟩
  | .b => ⟨1,by decide⟩
  | .aTmp => ⟨2,by decide⟩
  | .bTmp => ⟨3,by decide⟩
  | .output => ⟨4,by decide⟩

def stackOf (i : Index) : PStack :=
  if i.val = 0 then .a else if i.val = 1 then .b else if i.val = 2 then .aTmp else
    if i.val = 3 then .bTmp else .output

theorem index_of (i : Index) : stackIndex (stackOf i) = i := by
  fin_cases i <;> rfl

theorem of_index (s : PStack) : stackOf (stackIndex s) = s := by cases s <;> rfl

def stage (i : Index) : Phase := ⟨i.val,by omega⟩
def next (i : Index) : Phase := ⟨i.val+1,by omega⟩
def done : Phase := ⟨5,by decide⟩

def auxKey {ks : Nat} (i : Index) : Key ks := .inl (.inr (stackOf i))

def stackVals (ks symbols : Nat) (input output : List Bool) (A : Index → List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) : (s : Key ks) → List (Alphabet ks symbols s)
  | .inl (.inl false) => input
  | .inl (.inl true) => output
  | .inl (.inr a) => A (stackIndex a)
  | .inr a => S a

set_option backward.isDefEq.respectTransparency false in
theorem stackVals_update (ks symbols : Nat) (input output : List Bool) (A : Index → List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (i : Index) (xs : List Bool) :
    stackVals ks symbols input output (Function.update A i xs) S =
      Function.update (stackVals ks symbols input output A S) (auxKey i) xs := by
  funext s
  cases s with
  | inl p =>
    cases p with
    | inl b => cases b <;> simp [stackVals,auxKey,Function.update]
    | inr a =>
      by_cases h : a = stackOf i
      · subst a; simp [stackVals,auxKey,Function.update,index_of]
      · have hi : stackIndex a ≠ i := by
          intro he
          apply h
          calc
            a = stackOf (stackIndex a) := (of_index a).symm
            _ = stackOf i := congrArg stackOf he
        have hk : (Sum.inl (Sum.inr a) : Key ks) ≠ auxKey i := by
          simp [auxKey,h]
        change (Function.update A i xs) (stackIndex a) =
          (Function.update (stackVals ks symbols input output A S) (auxKey i) xs) (Sum.inl (Sum.inr a))
        rw [Function.update_of_ne hi,Function.update_of_ne hk]
        rfl
  | inr j => simp [stackVals,auxKey,Function.update]

def program (ks states symbols : Nat) (l : Phase) :
    Stmt (Alphabet ks symbols) Phase (AuxState states) :=
  if h : l.val < 5 then
    let i : Index := ⟨l.val,h⟩
    .pop (auxKey i) (fun v x => (v.1,v.2.1,x.isSome))
      (.branch (fun v => v.2.2) (.goto (fun _ => l)) (.goto (fun _ => next i)))
  else .goto (fun _ => done)

def machine (ks states symbols initial : Nat) : Turing.FinTM2 where
  K := Key ks
  k₀ := .inl (.inl false)
  k₁ := .inl (.inl true)
  Γ := Alphabet ks symbols
  Λ := Phase
  main := ⟨0,by decide⟩
  σ := AuxState states
  initialState := (false,clip states initial,false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols

def cfg (ks states symbols initial : Nat) (l : Phase) (answer : Bool) (v : Fin (states+1)) (flag : Bool)
    (input output : List Bool) (A : Index → List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols initial).Cfg := ⟨some l,(answer,v,flag),stackVals ks symbols input output A S⟩

set_option backward.isDefEq.respectTransparency false in
theorem step_cons (ks states symbols initial : Nat) (i : Index) (answer : Bool) (v : Fin (states+1))
    (flag : Bool) (input output : List Bool) (A : Index → List Bool) (S : Fin (ks+1) → List (Fin (symbols+1)))
    (x : Bool) (xs : List Bool) :
    (machine ks states symbols initial).step (cfg ks states symbols initial (stage i) answer v flag input output (Function.update A i (x::xs)) S) =
      some (cfg ks states symbols initial (stage i) answer v true input output (Function.update A i xs) S) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,stage,dif_pos i.isLt,stepAux,
    stackVals,auxKey,Function.update_self,index_of,List.head?_cons,Option.isSome_some,List.tail_cons]
  congr 1
  simp only [Bool.cond_true]
  congr 1
  have hu := stackVals_update ks symbols input output (Function.update A i (x::xs)) S i xs
  simp only [auxKey] at hu
  rw [← hu,Function.update_idem]

set_option backward.isDefEq.respectTransparency false in
theorem step_nil (ks states symbols initial : Nat) (i : Index) (answer : Bool) (v : Fin (states+1))
    (flag : Bool) (input output : List Bool) (A : Index → List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols initial).step (cfg ks states symbols initial (stage i) answer v flag input output (Function.update A i []) S) =
      some (cfg ks states symbols initial (next i) answer v false input output (Function.update A i []) S) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,stage,dif_pos i.isLt,stepAux,
    stackVals,auxKey,Function.update_self,index_of,List.head?_nil,Option.isSome_none,List.tail_nil]
  congr 1
  simp only [Bool.cond_false]
  congr 1
  have hu := stackVals_update ks symbols input output (Function.update A i []) S i []
  simp only [auxKey] at hu
  rw [← hu,Function.update_idem]

theorem sweep_one (ks states symbols initial : Nat) (i : Index) (answer : Bool) (v : Fin (states+1))
    (flag : Bool) (input output : List Bool) (A : Index → List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) (xs : List Bool) :
    runSteps (machine ks states symbols initial).step (xs.length+1)
      (cfg ks states symbols initial (stage i) answer v flag input output (Function.update A i xs) S) =
      some (cfg ks states symbols initial (next i) answer v false input output (Function.update A i []) S) := by
  induction xs generalizing flag with
  | nil =>
    change (machine ks states symbols initial).step
      (cfg ks states symbols initial (stage i) answer v flag input output (Function.update A i []) S) = _
    exact step_nil ks states symbols initial i answer v flag input output A S
  | cons x xs ih =>
    rw [List.length_cons,Nat.add_assoc,Nat.add_comm 1,← Nat.add_assoc,runSteps_front,step_cons]
    exact ih true

/-- Sweep every auxiliary arithmetic stack. The input, output and numeric core
stackVals are preserved, and the continuation label is active. -/
theorem sweep_all (ks states symbols initial : Nat) (answer : Bool) (v : Fin (states+1))
    (input output : List Bool) (bound : Nat) :
    ∀ (n : Nat) (a : Nat) (ha : a+n = 5) (A : Index → List Bool)
      (S : Fin (ks+1) → List (Fin (symbols+1))) (flag : Bool),
      (∀ i, i.val < a → A i = []) → (∀ i, (A i).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps (machine ks states symbols initial).step t
          (cfg ks states symbols initial ⟨a,by omega⟩ answer v flag input output A S) =
        some (cfg ks states symbols initial done answer v f input output (fun _ => []) S) := by
  intro n
  induction n with
  | zero =>
    intro a ha A S flag hempty hbound
    have ae : a = 5 := by omega
    have hA : A = fun _ => [] := by funext i; apply hempty; omega
    subst A
    have hl : (⟨a,by omega⟩ : Phase) = done := by apply Fin.ext; simp [done,ae]
    refine ⟨0,by simp,flag,?_⟩
    rw [hl]
    rfl
  | succ n ih =>
    intro a ha A S flag hempty hbound
    have halt : a < 5 := by omega
    let i : Index := ⟨a,halt⟩
    let A' := Function.update A i []
    have hempty' : ∀ j, j.val < a+1 → A' j = [] := by
      intro j hj
      by_cases heq : j = i
      · subst j; simp [A']
      · have hval : j.val ≠ a := by intro h; apply heq; exact Fin.ext h
        have hlt : j.val < a := by omega
        simpa [A',Function.update_of_ne heq] using hempty j hlt
    have hbound' : ∀ j, (A' j).length ≤ bound := by
      intro j
      by_cases heq : j = i
      · subst j; simp [A']
      · simpa [A',Function.update_of_ne heq] using hbound j
    obtain ⟨t,ht,f,hrun⟩ := ih (a+1) (by omega) A' S false hempty' hbound'
    have hstage : stage i = (⟨a,by omega⟩ : Phase) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Phase) := by apply Fin.ext; rfl
    have hone := sweep_one ks states symbols initial i answer v flag input output A S (A i)
    rw [Function.update_eq_self,hstage,hnext] at hone
    have htbound : (A i).length+1+t ≤ (n+1)*(bound+1) := by
      have hi := hbound i
      rw [Nat.add_mul,Nat.one_mul]
      omega
    refine ⟨(A i).length+1+t,by simpa using htbound,f,?_⟩
    rw [runSteps_add,hone]
    exact hrun

/-- A fresh sweep clears all five arithmetic stacks in at most five empty
checks plus their total lengths, while preserving the two Boolean I/O stacks
and all numeric core stacks. -/
theorem sweep_from_start (ks states symbols initial : Nat) (answer : Bool) (v : Fin (states+1))
    (flag : Bool) (input output : List Bool) (A : Index → List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (bound : Nat)
    (hbound : ∀ i, (A i).length ≤ bound) :
    ∃ t ≤ 5*(bound+1), ∃ f,
      runSteps (machine ks states symbols initial).step t
        (cfg ks states symbols initial ⟨0,by decide⟩ answer v flag input output A S) =
      some (cfg ks states symbols initial done answer v f input output (fun _ => []) S) := by
  exact sweep_all ks states symbols initial answer v input output bound 5 0 (by omega) A S flag
    (by intro i hi; omega) hbound

theorem done_stable (ks states symbols initial : Nat) (answer : Bool) (v : Fin (states+1))
    (flag : Bool) (input output : List Bool) (A : Index → List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols initial).step (cfg ks states symbols initial done answer v flag input output A S) =
      some (cfg ks states symbols initial done answer v flag input output A S) := by
  change some (stepAux (program ks states symbols done) (answer,v,flag) (stackVals ks symbols input output A S)) = _
  simp [program,done,stepAux,cfg]
  rfl

example :
    let A : Index → List Bool := fun i => if i.val = 0 then [true,true] else if i.val = 1 then [true] else []
    (runSteps (machine 0 1 2 0).step 8
      (cfg 0 1 2 0 ⟨0,by decide⟩ true ⟨0,by decide⟩ false [] [] A (fun _ => []))).map
      (fun c => c.stk (.inl (.inr .a))) = some [] := by
  change (Option.map (fun c => c.stk (.inl (.inr .a)))
    (runSteps (machine 0 1 2 0).step 8
      (cfg 0 1 2 0 ⟨0,by decide⟩ true ⟨0,by decide⟩ false [] []
        (fun i => if i.val = 0 then [true,true] else if i.val = 1 then [true] else []) (fun _ => []))) :
      Option (List Bool)) = some []
  decide

end Shared.ComplexityBridge.TM2AuxSweep
