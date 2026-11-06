import Shared.Codes.TM2ProgramHalt
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-! Quantitative refinement of mathlib's TM1-to-TM0 translation.
Costs count primitive post-Turing moves/writes, not binary encoding. -/
namespace Shared.ComplexityBridge.TM1GeneralTM0Costs
open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program (runSteps_add runSteps_front)

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

def maxCost : TM1.Stmt Γ Λ σ → Nat
  | .move _ q | .write _ q => 1 + maxCost q
  | .load _ q => maxCost q
  | .branch _ q r => max (maxCost q) (maxCost r)
  | .goto _ | .halt => 1

def cost : TM1.Stmt Γ Λ σ → σ → Tape Γ → Nat
  | .move d q, v, T => 1 + cost q v (T.move d)
  | .write f q, v, T => 1 + cost q v (T.write (f T.head v))
  | .load f q, v, T => cost q (f T.head v) T
  | .branch f q r, v, T => if f T.head v then cost q v T else cost r v T
  | .goto _, _, _ | .halt, _, _ => 1

omit [Inhabited Λ] [Inhabited σ] in
theorem cost_positive (s : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) : 0 < cost s v T := by
  induction s generalizing v T with
  | move d q ih => simp [cost]
  | write f q ih => simp [cost]
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr => cases h : f T.head v <;> simp [cost,h,ihq,ihr]
  | goto f => simp [cost]
  | halt => simp [cost]

omit [Inhabited Λ] [Inhabited σ] in
theorem cost_le_max (s : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) : cost s v T ≤ maxCost s := by
  induction s generalizing v T with
  | move d q ih => simpa [cost,maxCost] using Nat.add_le_add_left (ih v (T.move d)) 1
  | write f q ih => simpa [cost,maxCost] using Nat.add_le_add_left (ih v (T.write (f T.head v))) 1
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    cases h : f T.head v with
    | false => simpa [cost,maxCost,h] using le_trans (ihr v T) (le_max_right (maxCost q) (maxCost r))
    | true => simpa [cost,maxCost,h] using le_trans (ihq v T) (le_max_left (maxCost q) (maxCost r))
  | goto f => rfl
  | halt => rfl

theorem run_same_step {α : Type} (f : α → Option α) (x y : α) (d : Nat)
    (hd : 0 < d) (h : f x = f y) : runSteps f d x = runSteps f d y := by
  cases d with
  | zero => omega
  | succ d => rw [runSteps_front,runSteps_front,h]

/-- A statement is implemented by a positive number of actual post-Turing
steps, ending at exactly mathlib's translated configuration. -/
theorem statement_run (M : Λ → TM1.Stmt Γ Λ σ) (s : TM1.Stmt Γ Λ σ)
    (v : σ) (T : Tape Γ) :
    runSteps (TM0.step (TM1to0.tr M)) (cost s v T) ⟨(some s,v),T⟩ =
      some (TM1to0.trCfg M (TM1.stepAux s v T)) := by
  induction s generalizing v T with
  | move dir s ih =>
    change runSteps (TM0.step (TM1to0.tr M)) (1 + cost s v (T.move dir)) _ = _
    rw [show 1 + cost s v (T.move dir) = cost s v (T.move dir) + 1 by omega,runSteps_front]
    change runSteps (TM0.step (TM1to0.tr M)) (cost s v (T.move dir)) ⟨(some s,v),T.move dir⟩ = _
    exact ih v (T.move dir)
  | write f s ih =>
    change runSteps (TM0.step (TM1to0.tr M)) (1 + cost s v (T.write (f T.head v))) _ = _
    rw [show 1 + cost s v (T.write (f T.head v)) = cost s v (T.write (f T.head v)) + 1 by omega,runSteps_front]
    change runSteps (TM0.step (TM1to0.tr M)) (cost s v (T.write (f T.head v))) ⟨(some s,v),T.write (f T.head v)⟩ = _
    exact ih v (T.write (f T.head v))
  | load f s ih =>
    change runSteps (TM0.step (TM1to0.tr M)) (cost s (f T.head v) T) ⟨(some (.load f s),v),T⟩ = _
    rw [run_same_step _ _ ⟨(some s,f T.head v),T⟩ _ (cost_positive _ _ _) (by rfl)]
    exact ih (f T.head v) T
  | branch f s t ihs iht =>
    cases hf : f T.head v with
    | false =>
      simp only [cost,hf,Bool.false_eq_true,↓reduceIte,TM1.stepAux]
      rw [run_same_step _ _ ⟨(some t,v),T⟩ _ (cost_positive _ _ _) (by simp [TM0.step,TM1to0.tr,TM1to0.trAux,hf])]
      simpa [TM1.stepAux,hf] using iht v T
    | true =>
      simp only [cost,hf,↓reduceIte,TM1.stepAux]
      rw [run_same_step _ _ ⟨(some s,v),T⟩ _ (cost_positive _ _ _) (by simp [TM0.step,TM1to0.tr,TM1to0.trAux,hf])]
      simpa [TM1.stepAux,hf] using ihs v T
  | goto f => simp [cost,runSteps,TM0.step,TM1to0.tr,TM1to0.trAux,TM1to0.trCfg,TM1.stepAux,Tape.write_self]
  | halt => simp [cost,runSteps,TM0.step,TM1to0.tr,TM1to0.trAux,TM1to0.trCfg,TM1.stepAux,Tape.write_self]

noncomputable def statementLimit (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : Nat :=
  1 + S.sup (fun q => maxCost (M q))

omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
theorem statementLimit_bound (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (q : Λ) (h : q ∈ S) : maxCost (M q) ≤ statementLimit M S := by
  have hm := Finset.le_sup (f := fun q => maxCost (M q)) h
  dsimp [statementLimit]
  omega

/-- One successful source block yields an exact positive target run. -/
theorem one_block (M : Λ → TM1.Stmt Γ Λ σ) (x x' : TM1.Cfg Γ Λ σ)
    (q : Λ) (hq : x.l = some q) (hstep : TM1.step M x = some x') :
    ∃ d, 0 < d ∧ d ≤ maxCost (M q) ∧
      runSteps (TM0.step (TM1to0.tr M)) d (TM1to0.trCfg M x) = some (TM1to0.trCfg M x') := by
  cases x with
  | mk l v T =>
    cases l with
    | none => simp at hq
    | some q' =>
      simp only [Option.some.injEq] at hq
      subst q'
      have hx : TM1.stepAux (M q) v T = x' := by simpa [TM1.step] using hstep
      refine ⟨cost (M q) v T,cost_positive _ _ _,cost_le_max _ _ _,?_⟩
      simpa [TM1to0.trCfg,hx] using statement_run M (M q) v T

/-- Complete successful source runs, including those ending at halt, have
matching post-Turing runs with linear overhead and positive progress. -/
theorem run_bounded (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hs : TM1.Supports M S)
    (n : Nat) (x x' : TM1.Cfg Γ Λ σ) (hmem : x.l ∈ S.insertNone)
    (hrun : runSteps (TM1.step M) n x = some x') :
    ∃ d, n ≤ d ∧ d ≤ n * statementLimit M S ∧
      runSteps (TM0.step (TM1to0.tr M)) d (TM1to0.trCfg M x) = some (TM1to0.trCfg M x') := by
  induction n generalizing x with
  | zero =>
    change some x = some x' at hrun
    cases Option.some.inj hrun
    exact ⟨0,by omega,by simp,rfl⟩
  | succ n ih =>
    rw [runSteps_front] at hrun
    cases hstep : TM1.step M x with
    | none => rw [hstep] at hrun; contradiction
    | some mid =>
      rw [hstep] at hrun
      have hnext : mid.l ∈ S.insertNone := TM1.step_supports M hs (by rw [hstep]; rfl) hmem
      cases hq : x.l with
      | none =>
        cases x with
        | mk l v T => simp only at hq; subst l; contradiction
      | some q =>
        have hqmem : q ∈ S := by rw [hq] at hmem; exact Finset.some_mem_insertNone.1 hmem
        obtain ⟨d,hdpos,hd,hfirst⟩ := one_block M x mid q hq hstep
        obtain ⟨e,hepos,he,hrest⟩ := ih mid hnext hrun
        refine ⟨d+e,by omega,?_,?_⟩
        · have hbound := statementLimit_bound M S q hqmem
          rw [Nat.succ_mul]
          omega
        · rw [runSteps_add,hfirst]
          exact hrest

end Shared.ComplexityBridge.TM1GeneralTM0Costs
