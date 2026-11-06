import Shared.ComplexityBridge.TM2GateSweep

namespace Shared.ComplexityBridge.TM2GenericStackBound
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

/-- A finite statement block performs at most this many pushes, on any path.
No finiteness of the internal stack alphabets is assumed. -/
def pushBound {K Λ σ : Type} {Γ : K → Type} : Stmt Γ Λ σ → Nat
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => max (pushBound q) (pushBound r)
  | .goto _ | .halt => 0

set_option backward.isDefEq.respectTransparency false in
/-- A single statement block cannot increase a stack beyond its push count. -/
theorem stepAux_length {K Λ σ : Type} [DecidableEq K] {Γ : K → Type}
    (q : Stmt Γ Λ σ) (v : σ) (S : (k : K) → List (Γ k)) (k : K) :
    ((stepAux q v S).stk k).length ≤ (S k).length + pushBound q := by
  induction q generalizing v S with
  | halt => simp [stepAux,pushBound]
  | goto f => simp [stepAux,pushBound]
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | push j f q ih =>
    simp only [stepAux,pushBound]
    have h := ih v (Function.update S j (f v :: S j))
    by_cases hk : k = j
    · subst k
      simp only [Function.update_self,List.length_cons] at h
      omega
    · have hu : (Function.update S j (f v :: S j)) k = S k := Function.update_of_ne hk _ _
      rw [hu] at h
      omega
  | pop j f q ih =>
    simp only [stepAux,pushBound]
    have h := ih (f v (S j).head?) (Function.update S j (S j).tail)
    by_cases hk : k = j
    · subst k
      simp only [Function.update_self] at h
      have ht : (S j).tail.length ≤ (S j).length := by simp
      omega
    · have hu : (Function.update S j (S j).tail) k = S k := Function.update_of_ne hk _ _
      rw [hu] at h
      exact h
  | branch f q r ihq ihr =>
    simp only [stepAux,pushBound]
    cases hf : f v with
    | true =>
      simp only [hf,Bool.cond_true]
      have h := ihq v S
      have hmax : pushBound q ≤ max (pushBound q) (pushBound r) := le_max_left _ _
      omega
    | false =>
      simp only [hf,Bool.cond_false]
      have h := ihr v S
      have hmax : pushBound r ≤ max (pushBound q) (pushBound r) := le_max_right _ _
      omega

/-- A proof-side constant bounding every finite control block. -/
noncomputable def tableBound (tm : Turing.FinTM2) : Nat := by
  classical
  letI := tm.ΛFin
  exact Finset.univ.sup (fun l : tm.Λ => pushBound (tm.m l))

theorem block_le_table (tm : Turing.FinTM2) (l : tm.Λ) : pushBound (tm.m l) ≤ tableBound tm := by
  classical
  letI := tm.ΛFin
  exact Finset.le_sup (f := fun l : tm.Λ => pushBound (tm.m l)) (Finset.mem_univ l)

set_option backward.isDefEq.respectTransparency false in
theorem step_length (tm : Turing.FinTM2) (c d : tm.Cfg) (h : tm.step c = some d) (k : tm.K) :
    (d.stk k).length ≤ (c.stk k).length + tableBound tm := by
  cases c with
  | mk l v S =>
    cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (tm.m l) v S) = some d at h
      cases h
      change ((stepAux (tm.m l) v S).stk k).length ≤ (S k).length + tableBound tm
      have h := stepAux_length (tm.m l) v S k
      have ht := block_le_table tm l
      omega

set_option backward.isDefEq.respectTransparency false in
/-- Every stack in a t-block run grows by at most t times the fixed table
constant, including for machines with infinite internal alphabets. -/
theorem run_length (tm : Turing.FinTM2) (n : Nat) (c d : tm.Cfg)
    (h : runSteps tm.step n c = some d) (k : tm.K) :
    (d.stk k).length ≤ (c.stk k).length + n * tableBound tm := by
  induction n generalizing c with
  | zero =>
    change some c = some d at h
    cases h
    simp
  | succ n ih =>
    rw [runSteps_front] at h
    change (tm.step c).bind (runSteps tm.step n) = some d at h
    cases hs : tm.step c with
    | none =>
      rw [hs] at h
      contradiction
    | some c' =>
      rw [hs] at h
      have hr : runSteps tm.step n c' = some d := h
      have hi := ih c' hr
      have hs' := step_length tm c c' hs k
      rw [Nat.succ_mul]
      omega

theorem init_length (tm : Turing.FinTM2) (bits : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm bits).stk k).length ≤ bits.length := by
  classical
  by_cases h : k = tm.k₀
  · subst k; simp [Turing.initList]
  · simp [Turing.initList,h]

/-- Bound on each stack from the actual input configuration. -/
theorem run_from_input_length (tm : Turing.FinTM2) (bits : List (tm.Γ tm.k₀)) (n : Nat) (d : tm.Cfg)
    (h : runSteps tm.step n (Turing.initList tm bits) = some d) (k : tm.K) :
    (d.stk k).length ≤ bits.length + n * tableBound tm := by
  have hr := run_length tm n (Turing.initList tm bits) d h k
  have hi := init_length tm bits k
  omega

end Shared.ComplexityBridge.TM2GenericStackBound
