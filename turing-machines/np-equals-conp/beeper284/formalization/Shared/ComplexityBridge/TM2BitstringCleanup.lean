import Shared.ComplexityBridge.TM2BitstringTransfer
import Shared.ComplexityBridge.TM2Cleanup

/-! Sweep all numeric core stacks without changing the completed Boolean
output. The initial Boolean scratch must be empty. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BitstringCleanup
open Turing.TM2 Shared.ComplexityBridge.TM2Combined Shared.ComplexityBridge.TM2Cleanup
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program

def program (ks symbols : Nat) (l : Fin (ks+2)) :
    Stmt (Alphabet ks symbols) (Fin (ks+2)) Bool :=
  if h : l.val < ks+1 then
    let i : Fin (ks+1) := ⟨l.val,h⟩
    .pop (.inr i) (fun _ x => x.isSome)
      (.branch id (.goto (fun _ => l)) (.goto (fun _ => next i)))
  else .load (fun _ => false) .halt

def machine (ks symbols : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Fin (ks+2)
  main := ⟨0,by omega⟩
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks symbols

def cfg (ks symbols : Nat) (l : Fin (ks+2)) (flag : Bool) (output : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) : (machine ks symbols).Cfg :=
  ⟨some l,flag,embedStacks ks symbols [] output S⟩

theorem step_cons (ks symbols : Nat) (i : Fin (ks+1)) (flag : Bool) (output : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (x : Fin (symbols+1)) (xs : List (Fin (symbols+1))) :
    (machine ks symbols).step (cfg ks symbols (stage i) flag output (Function.update S i (x::xs))) =
      some (cfg ks symbols (stage i) true output (Function.update S i xs)) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,stage,dif_pos i.isLt,
    stepAux,embedStacks,Function.update_self,List.head?_cons,Option.isSome_some,List.tail_cons,id_eq]
  congr 1
  simp only [Bool.cond_true]
  congr 1
  rw [← embedStacks_update,Function.update_idem]

theorem step_nil (ks symbols : Nat) (i : Fin (ks+1)) (flag : Bool) (output : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks symbols).step (cfg ks symbols (stage i) flag output (Function.update S i [])) =
      some (cfg ks symbols (next i) false output (Function.update S i [])) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,stage,dif_pos i.isLt,
    stepAux,embedStacks,Function.update_self,List.head?_nil,Option.isSome_none,List.tail_nil,id_eq]
  congr 1
  simp only [Bool.cond_false]
  congr 1
  rw [← embedStacks_update,Function.update_idem]

theorem sweep_one (ks symbols : Nat) (i : Fin (ks+1)) (flag : Bool) (output : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (xs : List (Fin (symbols+1))) :
    runSteps (machine ks symbols).step (xs.length+1)
      (cfg ks symbols (stage i) flag output (Function.update S i xs)) =
      some (cfg ks symbols (next i) false output (Function.update S i [])) := by
  induction xs generalizing flag with
  | nil => exact step_nil ks symbols i flag output S
  | cons x xs ih =>
    rw [List.length_cons,Nat.add_assoc,Nat.add_comm 1,← Nat.add_assoc,runSteps_front,step_cons]
    exact ih true

/-- All previously visited numeric stacks remain empty, and the Boolean
output list stays byte-for-byte unchanged through the sweep. -/
theorem sweep_suffix (ks symbols : Nat) (output : List Bool) (bound n : Nat) :
    ∀ (a : Nat) (ha : a+n = ks+1) (S : Fin (ks+1) → List (Fin (symbols+1))) (flag : Bool),
      (∀ k, k.val < a → S k = []) → (∀ k, (S k).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps (machine ks symbols).step t (cfg ks symbols ⟨a,by omega⟩ flag output S) =
          some (cfg ks symbols (sentinel ks) f output (fun _ => [])) := by
  induction n with
  | zero =>
    intro a ha S flag hempty hbound
    have ae : a = ks+1 := by omega
    have hS : S = fun _ => [] := by
      funext k
      apply hempty
      omega
    subst S
    have hl : (⟨a,by omega⟩ : Fin (ks+2)) = sentinel ks := by apply Fin.ext; simp [sentinel,ae]
    refine ⟨0,by simp,flag,?_⟩
    rw [hl]
    rfl
  | succ n ih =>
    intro a ha S flag hempty hbound
    have halt : a < ks+1 := by omega
    let i : Fin (ks+1) := ⟨a,halt⟩
    let S' := Function.update S i []
    have hempty' : ∀ k, k.val < a+1 → S' k = [] := by
      intro k hk
      by_cases heq : k = i
      · subst k; simp [S']
      · have hval : k.val ≠ a := by
          intro h
          apply heq
          exact Fin.ext h
        have hlt : k.val < a := by omega
        simpa [S',Function.update_of_ne heq] using hempty k hlt
    have hbound' : ∀ k, (S' k).length ≤ bound := by
      intro k
      by_cases heq : k = i
      · subst k; simp [S']
      · simpa [S',Function.update_of_ne heq] using hbound k
    obtain ⟨t,ht,f,hrun⟩ := ih (a+1) (by omega) S' false hempty' hbound'
    have hstage : stage i = (⟨a,by omega⟩ : Fin (ks+2)) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Fin (ks+2)) := by apply Fin.ext; rfl
    have hone := sweep_one ks symbols i flag output S (S i)
    rw [Function.update_eq_self,hstage,hnext] at hone
    have htbound : (S i).length+1+t ≤ (n+1)*(bound+1) := by
      have hi := hbound i
      rw [Nat.add_mul,Nat.one_mul]
      omega
    refine ⟨(S i).length+1+t,by simpa using htbound,f,?_⟩
    rw [runSteps_add,hone]
    exact hrun

/-- Reset the complete internal state, retaining the arbitrary output list. -/
theorem finish (ks symbols : Nat) (flag : Bool) (output : List Bool) :
    (machine ks symbols).step (cfg ks symbols (sentinel ks) flag output (fun _ => [])) =
      some (Turing.haltList (machine ks symbols) output) := by
  have hn : ¬ (sentinel ks).val < ks+1 := by simp [sentinel]
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,dif_neg hn,stepAux]
  congr 1
  change Cfg.mk none false (embedStacks ks symbols [] output (fun _ => [])) =
    Turing.haltList (machine ks symbols) output
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [machine,embedStacks]
  | inr j => simp [machine,embedStacks]

/-- From empty Boolean scratch, every numeric stack is cleared and the
canonical halt configuration retains exactly the supplied output. -/
theorem sweep_all (ks symbols : Nat) (output : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (flag : Bool) (bound : Nat)
    (hbound : ∀ k, (S k).length ≤ bound) :
    ∃ t ≤ (ks+1)*(bound+1)+1,
      runSteps (machine ks symbols).step t (cfg ks symbols ⟨0,by omega⟩ flag output S) =
        some (Turing.haltList (machine ks symbols) output) := by
  obtain ⟨t,ht,f,hrun⟩ := sweep_suffix ks symbols output bound (ks+1)
    0 (by omega) S flag (by intro k hk; omega) hbound
  refine ⟨t+1,by omega,?_⟩
  rw [runSteps_add,hrun]
  exact finish ks symbols f output

end Shared.ComplexityBridge.TM2BitstringCleanup
