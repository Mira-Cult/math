import Shared.ComplexityBridge.TM2CutoffGate

namespace Shared.ComplexityBridge.TM2GateSweep
open Turing.TM2 Shared.Codes.TM2Program Shared.ComplexityBridge.TM2Symbols
abbrev Key := Shared.ComplexityBridge.TM2CutoffGate.Key
abbrev Index := Fin 9
abbrev Phase := Fin 10

/-- Every gate stack except its input stack, in a fixed, executable order. -/
def auxKey (i : Index) : Key :=
  if i.val = 0 then .inl true else
  if i.val = 1 then .inr (.inl ()) else
  if i.val = 2 then .inr (.inr (.inl false)) else
  if i.val = 3 then .inr (.inr (.inl true)) else
  if i.val = 4 then .inr (.inr (.inr .a)) else
  if i.val = 5 then .inr (.inr (.inr .b)) else
  if i.val = 6 then .inr (.inr (.inr .aTmp)) else
  if i.val = 7 then .inr (.inr (.inr .bTmp)) else
    .inr (.inr (.inr .output))

def auxIndex : Key → Option Index
  | .inl false => none
  | .inl true => some ⟨0,by decide⟩
  | .inr (.inl _) => some ⟨1,by decide⟩
  | .inr (.inr (.inl false)) => some ⟨2,by decide⟩
  | .inr (.inr (.inl true)) => some ⟨3,by decide⟩
  | .inr (.inr (.inr .a)) => some ⟨4,by decide⟩
  | .inr (.inr (.inr .b)) => some ⟨5,by decide⟩
  | .inr (.inr (.inr .aTmp)) => some ⟨6,by decide⟩
  | .inr (.inr (.inr .bTmp)) => some ⟨7,by decide⟩
  | .inr (.inr (.inr .output)) => some ⟨8,by decide⟩

theorem index_key (i : Index) : auxIndex (auxKey i) = some i := by fin_cases i <;> rfl

theorem key_index (q : Key) (i : Index) (h : auxIndex q = some i) : auxKey i = q := by
  cases q with
  | inl b => cases b <;> simp [auxIndex] at h; cases h; rfl
  | inr q => cases q with
    | inl u => cases u; simp [auxIndex] at h; cases h; rfl
    | inr q => cases q with
      | inl b => cases b <;> simp [auxIndex] at h <;> cases h <;> rfl
      | inr a => cases a <;> simp [auxIndex] at h <;> cases h <;> rfl

def stackVals (input : List Bool) (A : Index → List Bool) : Key → List Bool :=
  fun q => match auxIndex q with | none => input | some i => A i

@[simp] theorem stackVals_aux (input : List Bool) (A : Index → List Bool) (i : Index) :
    stackVals input A (auxKey i) = A i := by simp [stackVals,index_key]

theorem stackVals_update (input : List Bool) (A : Index → List Bool) (i : Index) (xs : List Bool) :
    stackVals input (Function.update A i xs) = Function.update (stackVals input A) (auxKey i) xs := by
  funext q
  cases hq : auxIndex q with
  | none =>
    have hne : q ≠ auxKey i := by intro he; subst q; rw [index_key] at hq; contradiction
    simp [stackVals,hq,Function.update_of_ne hne]
  | some j =>
    by_cases h : j = i
    · subst j
      have he := key_index q i hq
      subst q
      simp [stackVals,index_key]
    · have hne : q ≠ auxKey i := by
        intro he; subst q; rw [index_key] at hq; exact h (Option.some.inj hq.symm)
      simp [stackVals,hq,Function.update_of_ne h,Function.update_of_ne hne]

/-- A gate stack family decomposes into its input and its nine other stacks. -/
theorem stackVals_eta (S : Key → List Bool) :
    stackVals (S (.inl false)) (fun i => S (auxKey i)) = S := by
  funext q
  cases h : auxIndex q with
  | some i => simp only [stackVals,h]; rw [key_index q i h]
  | none =>
    have hq : q = .inl false := by
      cases q with
      | inl b => cases b <;> simp [auxIndex] at h ⊢
      | inr q => cases q with
        | inl u => cases u; simp [auxIndex] at h
        | inr q => cases q with
          | inl b => cases b <;> simp [auxIndex] at h
          | inr a => cases a <;> simp [auxIndex] at h
    subst q
    rfl

def stage (i : Index) : Phase := ⟨i.val,by omega⟩
def next (i : Index) : Phase := ⟨i.val+1,by omega⟩
def done : Phase := ⟨9,by decide⟩

/-- The first state bit carries the branch choice; the second is a pop flag. -/
def program (l : Phase) : Stmt (fun _ : Key => Bool) Phase (Bool × Bool) :=
  if h : l.val < 9 then
    let i : Index := ⟨l.val,h⟩
    .pop (auxKey i) (fun v x => (v.1,x.isSome))
      (.branch Prod.snd (.goto (fun _ => l)) (.goto (fun _ => next i)))
  else .goto (fun _ => done)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inl false
  k₁ := .inl true
  Γ := fun _ => Bool
  Λ := Phase
  main := ⟨0,by decide⟩
  σ := Bool × Bool
  initialState := (false,false)
  m := program

def cfg (l : Phase) (answer flag : Bool) (input : List Bool) (A : Index → List Bool) : machine.Cfg :=
  ⟨some l,(answer,flag),stackVals input A⟩

set_option backward.isDefEq.respectTransparency false in
theorem step_cons (i : Index) (answer flag : Bool) (input : List Bool) (A : Index → List Bool)
    (x : Bool) (xs : List Bool) :
    machine.step (cfg (stage i) answer flag input (Function.update A i (x::xs))) =
      some (cfg (stage i) answer true input (Function.update A i xs)) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,stage,dif_pos i.isLt,stepAux,
    stackVals_aux,Function.update_self,List.head?_cons,Option.isSome_some,List.tail_cons]
  congr 1
  simp only [Bool.cond_true]
  congr 1
  have hu := stackVals_update input (Function.update A i (x::xs)) i xs
  rw [← hu,Function.update_idem]

set_option backward.isDefEq.respectTransparency false in
theorem step_nil (i : Index) (answer flag : Bool) (input : List Bool) (A : Index → List Bool) :
    machine.step (cfg (stage i) answer flag input (Function.update A i [])) =
      some (cfg (next i) answer false input (Function.update A i [])) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,stage,dif_pos i.isLt,stepAux,
    stackVals_aux,Function.update_self,List.head?_nil,Option.isSome_none,List.tail_nil]
  congr 1
  simp only [Bool.cond_false]
  congr 1
  have hu := stackVals_update input (Function.update A i []) i []
  rw [← hu,Function.update_idem]

theorem sweep_one (i : Index) (answer flag : Bool) (input : List Bool) (A : Index → List Bool) (xs : List Bool) :
    runSteps machine.step (xs.length+1) (cfg (stage i) answer flag input (Function.update A i xs)) =
      some (cfg (next i) answer false input (Function.update A i [])) := by
  induction xs generalizing flag with
  | nil => exact step_nil i answer flag input A
  | cons x xs ih =>
    rw [List.length_cons,Nat.add_assoc,Nat.add_comm 1,← Nat.add_assoc,runSteps_front,step_cons]
    exact ih true

/-- All nine gate work stacks are cleared, while the input and branch bit are
preserved. Each pop and each empty-stack test costs one TM2 block. -/
theorem sweep_all (answer : Bool) (input : List Bool) (bound : Nat) :
    ∀ (n a : Nat) (ha : a+n = 9) (A : Index → List Bool) (flag : Bool),
      (∀ i, i.val < a → A i = []) → (∀ i, (A i).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps machine.step t (cfg ⟨a,by omega⟩ answer flag input A) =
          some (cfg done answer f input (fun _ => [])) := by
  intro n
  induction n with
  | zero =>
    intro a ha A flag hempty hbound
    have ae : a = 9 := by omega
    have hA : A = fun _ => [] := by funext i; apply hempty; omega
    subst A
    have hl : (⟨a,by omega⟩ : Phase) = done := by apply Fin.ext; simp [done,ae]
    refine ⟨0,by simp,flag,?_⟩
    rw [hl]
    rfl
  | succ n ih =>
    intro a ha A flag hempty hbound
    have halt : a < 9 := by omega
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
    obtain ⟨t,ht,f,hrun⟩ := ih (a+1) (by omega) A' false hempty' hbound'
    have hstage : stage i = (⟨a,by omega⟩ : Phase) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Phase) := by apply Fin.ext; rfl
    have hone := sweep_one i answer flag input A (A i)
    rw [Function.update_eq_self,hstage,hnext] at hone
    have htbound : (A i).length+1+t ≤ (n+1)*(bound+1) := by
      have hi := hbound i
      rw [Nat.add_mul,Nat.one_mul]
      omega
    refine ⟨(A i).length+1+t,by simpa using htbound,f,?_⟩
    rw [runSteps_add,hone]
    exact hrun

theorem sweep_from_start (answer flag : Bool) (input : List Bool) (A : Index → List Bool) (bound : Nat)
    (hbound : ∀ i, (A i).length ≤ bound) :
    ∃ t ≤ 9*(bound+1), ∃ f,
      runSteps machine.step t (cfg ⟨0,by decide⟩ answer flag input A) =
        some (cfg done answer f input (fun _ => [])) := by
  exact sweep_all answer input bound 9 0 (by omega) A flag (by intro i hi; omega) hbound

end Shared.ComplexityBridge.TM2GateSweep
