import Shared.ComplexityBridge.TM2StackBound

namespace Shared.ComplexityBridge.TM2Cleanup
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.ComplexityBridge.TM2Combined
open Shared.ComplexityBridge.TM2FiniteReverse Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2BooleanOutput

def stage {ks : Nat} (i : Fin (ks+1)) : Fin (ks+2) := ⟨i.val,by omega⟩
def next {ks : Nat} (i : Fin (ks+1)) : Fin (ks+2) := ⟨i.val+1,by omega⟩
def sentinel (ks : Nat) : Fin (ks+2) := ⟨ks+1,by omega⟩

def program (ks states symbols initial : Nat) (l : Fin (ks+2)) :
    Stmt (Alphabet ks symbols) (Fin (ks+2)) (Bool × Fin (states+1) × Bool) :=
  if h : l.val < ks+1 then
    let i : Fin (ks+1) := ⟨l.val,h⟩
    .pop (.inr i) (fun v x => (v.1,v.2.1,x.isSome))
      (.branch (fun v => v.2.2) (.goto (fun _ => l)) (.goto (fun _ => next i)))
  else
    .push (.inl true) (fun v => v.1)
      (.load (fun _ => (false,clip states initial,false)) .halt)

def cleaner (ks states symbols initial : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Fin (ks+2)
  main := ⟨0,by omega⟩
  σ := Bool × Fin (states+1) × Bool
  initialState := (false,clip states initial,false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols initial

def cfg (ks states symbols initial : Nat) (l : Fin (ks+2))
    (answer : Bool) (v : Fin (states+1)) (flag : Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) : (cleaner ks states symbols initial).Cfg :=
  ⟨some l,(answer,v,flag),embedStacks ks symbols [] [] S⟩

set_option backward.isDefEq.respectTransparency false in
theorem step_cons (ks states symbols initial : Nat) (i : Fin (ks+1))
    (answer : Bool) (v : Fin (states+1)) (flag : Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (x : Fin (symbols+1)) (xs : List (Fin (symbols+1))) :
    (cleaner ks states symbols initial).step (cfg ks states symbols initial (stage i) answer v flag (Function.update S i (x::xs))) =
      some (cfg ks states symbols initial (stage i) answer v true (Function.update S i xs)) := by
  simp only [Turing.FinTM2.step, Turing.TM2.step, cleaner, cfg, program, stage, dif_pos i.isLt,
    stepAux, embedStacks, Function.update_self, List.head?_cons, Option.isSome_some, List.tail_cons]
  congr 1
  simp only [Bool.cond_true]
  congr 1
  rw [← embedStacks_update, Function.update_idem]

set_option backward.isDefEq.respectTransparency false in
theorem step_nil (ks states symbols initial : Nat) (i : Fin (ks+1))
    (answer : Bool) (v : Fin (states+1)) (flag : Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (cleaner ks states symbols initial).step (cfg ks states symbols initial (stage i) answer v flag (Function.update S i [])) =
      some (cfg ks states symbols initial (next i) answer v false (Function.update S i [])) := by
  simp only [Turing.FinTM2.step, Turing.TM2.step, cleaner, cfg, program, stage, dif_pos i.isLt,
    stepAux, embedStacks, Function.update_self, List.head?_nil, Option.isSome_none, List.tail_nil]
  congr 1
  simp only [Bool.cond_false]
  congr 1
  rw [← embedStacks_update, Function.update_idem]

/-- Pop all symbols from one stack. Each symbol consumes exactly one block,
then one empty-stack block dispatches to the next stack. -/
theorem sweep_one (ks states symbols initial : Nat) (i : Fin (ks+1))
    (answer : Bool) (v : Fin (states+1)) (flag : Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (xs : List (Fin (symbols+1))) :
    runSteps (cleaner ks states symbols initial).step (xs.length+1)
      (cfg ks states symbols initial (stage i) answer v flag (Function.update S i xs)) =
      some (cfg ks states symbols initial (next i) answer v false (Function.update S i [])) := by
  induction xs generalizing flag with
  | nil =>
    change (cleaner ks states symbols initial).step
      (cfg ks states symbols initial (stage i) answer v flag (Function.update S i [])) = _
    exact step_nil ks states symbols initial i answer v flag S
  | cons x xs ih =>
    rw [List.length_cons, Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc, runSteps_front,
      step_cons]
    exact ih true

/-- Sweep a suffix of the core stack indices. Previously swept stacks must
be empty, and the next-label arithmetic is explicit. -/
theorem sweep_suffix (ks states symbols initial : Nat) (answer : Bool)
    (v : Fin (states+1)) (bound n : Nat) :
    ∀ (a : Nat) (ha : a+n = ks+1) (S : Fin (ks+1) → List (Fin (symbols+1))) (flag : Bool),
      (∀ k, k.val < a → S k = []) → (∀ k, (S k).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps (cleaner ks states symbols initial).step t
          (cfg ks states symbols initial ⟨a,by omega⟩ answer v flag S) =
          some (cfg ks states symbols initial (sentinel ks) answer v f (fun _ => [])) := by
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
        simpa [S', Function.update_of_ne heq] using hempty k hlt
    have hbound' : ∀ k, (S' k).length ≤ bound := by
      intro k
      by_cases heq : k = i
      · subst k; simp [S']
      · simpa [S', Function.update_of_ne heq] using hbound k
    obtain ⟨t,ht,f,hrun⟩ := ih (a+1) (by omega) S' false hempty' hbound'
    have hstage : stage i = (⟨a,by omega⟩ : Fin (ks+2)) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Fin (ks+2)) := by apply Fin.ext; rfl
    have hone := sweep_one ks states symbols initial i answer v flag S (S i)
    rw [Function.update_eq_self, hstage, hnext] at hone
    have htbound : (S i).length+1+t ≤ (n+1)*(bound+1) := by
      have hi := hbound i
      rw [Nat.add_mul, Nat.one_mul]
      omega
    refine ⟨(S i).length+1+t, by simpa using htbound, f, ?_⟩
    rw [runSteps_add, hone]
    exact hrun

/-- After the last stack, emit the stored Boolean, reset the whole internal
state, and halt in exactly the library's canonical output configuration. -/
theorem finish (ks states symbols initial : Nat) (answer : Bool)
    (v : Fin (states+1)) (flag : Bool) :
    (cleaner ks states symbols initial).step
      (cfg ks states symbols initial (sentinel ks) answer v flag (fun _ => [])) =
      some (Turing.haltList (cleaner ks states symbols initial) [answer]) := by
  have hn : ¬(sentinel ks).val < ks+1 := by simp [sentinel]
  simp only [Turing.FinTM2.step, Turing.TM2.step, cleaner, cfg, program, dif_neg hn, stepAux]
  congr 1
  change Cfg.mk none (false,clip states initial,false)
    (Function.update (embedStacks ks symbols [] [] (fun _ => [])) (.inl true) [answer]) =
      Turing.haltList (cleaner ks states symbols initial) [answer]
  congr 1
  funext k
  cases k with
  | inl b =>
    cases b <;> simp [cleaner, embedStacks, Function.update]
    rfl
  | inr j => simp [cleaner, embedStacks, Function.update]

/-- All core stacks are emptied and the saved answer is returned with the
exact library halt convention, within the stated uniform stack bound. -/
theorem sweep_all (ks states symbols initial : Nat) (answer : Bool)
    (v : Fin (states+1)) (flag : Bool) (S : Fin (ks+1) → List (Fin (symbols+1)))
    (bound : Nat) (hbound : ∀ k, (S k).length ≤ bound) :
    ∃ t ≤ (ks+1)*(bound+1)+1,
      runSteps (cleaner ks states symbols initial).step t
        (cfg ks states symbols initial ⟨0,by omega⟩ answer v flag S) =
        some (Turing.haltList (cleaner ks states symbols initial) [answer]) := by
  obtain ⟨t,ht,f,hrun⟩ := sweep_suffix ks states symbols initial answer v bound (ks+1)
    0 (by omega) S flag (by intro k hk; omega) hbound
  refine ⟨t+1,by omega,?_⟩
  rw [runSteps_add, hrun]
  change (cleaner ks states symbols initial).step
    (cfg ks states symbols initial (sentinel ks) answer v f (fun _ => [])) = _
  exact finish ks states symbols initial answer v f

/-- Reading the numeric output head recovers the Boolean accepted by the
existing strict singleton decoder. -/
theorem decodeStack_head (symbols z o : Nat) (xs : List (Fin (symbols+1))) (b : Bool)
    (h : decodeStack (z,o,xs.map Fin.val) = some b) :
    (xs.head?.map (fun x => x.val == o)).getD false = b := by
  unfold decodeStack at h
  split at h
  · contradiction
  · rename_i hne
    split at h
    · rename_i hz
      have hb : b = false := by simpa using h.symm
      subst b
      cases xs with
      | nil => simp at hz
      | cons x rest =>
        simp only [List.map_cons, List.cons.injEq] at hz
        have hx : x.val = z := hz.1
        simp [hx, hne]
    · split at h
      · rename_i ho
        have hb : b = true := by simpa using h.symm
        subst b
        cases xs with
        | nil => simp at ho
        | cons x rest =>
          simp only [List.map_cons, List.cons.injEq] at ho
          have hx : x.val = o := ho.1
          simp [hx]
      · contradiction

abbrev SweepStmt (ks states symbols : Nat) :=
  Stmt (Alphabet ks symbols) (Fin (ks+2)) (Bool × Fin (states+1) × Bool)

def retagStmt (ks states symbols : Nat) : SweepStmt ks states symbols →
    Stmt (Alphabet ks symbols) (Unit ⊕ Fin (ks+2)) (Bool × Fin (states+1) × Bool)
  | .push k f q => .push k f (retagStmt ks states symbols q)
  | .peek k f q => .peek k f (retagStmt ks states symbols q)
  | .pop k f q => .pop k f (retagStmt ks states symbols q)
  | .load f q => .load f (retagStmt ks states symbols q)
  | .branch f a b => .branch f (retagStmt ks states symbols a) (retagStmt ks states symbols b)
  | .goto f => .goto (fun v => .inr (f v))
  | .halt => .halt

def retagCfg (ks states symbols : Nat)
    (c : Cfg (Alphabet ks symbols) (Fin (ks+2)) (Bool × Fin (states+1) × Bool)) :
    Cfg (Alphabet ks symbols) (Unit ⊕ Fin (ks+2)) (Bool × Fin (states+1) × Bool) :=
  ⟨c.l.map Sum.inr,c.var,c.stk⟩

theorem retag_stepAux (ks states symbols : Nat) (q : SweepStmt ks states symbols)
    (v : Bool × Fin (states+1) × Bool) (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (retagStmt ks states symbols q) v S = retagCfg ks states symbols (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [retagStmt,stepAux,h,iha,ihb]

/-- A prelude reads the output head into the saved answer, then dispatches to
the cleanup program. It uses a Boolean output stack. -/
def outputProgram (ks states symbols initial output one : Nat) : Unit ⊕ Fin (ks+2) →
    Stmt (Alphabet ks symbols) (Unit ⊕ Fin (ks+2)) (Bool × Fin (states+1) × Bool)
  | .inl () => .peek (.inr (clip ks output))
      (fun v h => ((h.map (fun x => x.val == one)).getD false,v.2.1,v.2.2))
      (.goto (fun _ => .inr ⟨0,by omega⟩))
  | .inr l => retagStmt ks states symbols (program ks states symbols initial l)

def outputCleaner (ks states symbols initial output one : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Unit ⊕ Fin (ks+2)
  main := .inl ()
  σ := Bool × Fin (states+1) × Bool
  initialState := (false,clip states initial,false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := outputProgram ks states symbols initial output one

set_option backward.isDefEq.respectTransparency false in
theorem output_cleaner_step (ks states symbols initial output one : Nat)
    (c : (cleaner ks states symbols initial).Cfg) :
    (outputCleaner ks states symbols initial output one).step (retagCfg ks states symbols c) =
      ((cleaner ks states symbols initial).step c).map (retagCfg ks states symbols) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (retagStmt ks states symbols (program ks states symbols initial l)) v S) = _
      rw [retag_stepAux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem output_cleaner_run (ks states symbols initial output one : Nat)
    (c : (cleaner ks states symbols initial).Cfg) (n : Nat) :
    runSteps (outputCleaner ks states symbols initial output one).step n (retagCfg ks states symbols c) =
      (runSteps (cleaner ks states symbols initial).step n c).map (retagCfg ks states symbols) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front, runSteps_front, output_cleaner_step]
    cases h : (cleaner ks states symbols initial).step c with
    | none => rfl
    | some c' => exact ih c'

def fetchCfg (ks states symbols initial output one : Nat) (v : Fin (states+1)) (flag : Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) : (outputCleaner ks states symbols initial output one).Cfg :=
  ⟨some (.inl ()),(false,v,flag),embedStacks ks symbols [] [] S⟩

/-- The prelude reads precisely the result accepted by the strict numeric
singleton decoder. -/
theorem fetch_step (ks states symbols initial output zcode one : Nat)
    (v : Fin (states+1)) (flag : Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) (b : Bool)
    (h : decodeStack (zcode,one,(S (clip ks output)).map Fin.val) = some b) :
    (outputCleaner ks states symbols initial output one).step
      (fetchCfg ks states symbols initial output one v flag S) =
        some (retagCfg ks states symbols (cfg ks states symbols initial ⟨0,by omega⟩ b v flag S)) := by
  have hb := decodeStack_head symbols zcode one (S (clip ks output)) b h
  change some (Cfg.mk (some (Sum.inr (⟨0,by omega⟩ : Fin (ks+2)) : Unit ⊕ Fin (ks+2)))
    (((S (clip ks output)).head?.map (fun x => x.val == one)).getD false,v,flag)
      (embedStacks ks symbols [] [] S)) = _
  rw [hb]
  rfl

/-- Both wrappers have exactly the same canonical final output configuration. -/
theorem retag_halt (ks states symbols initial output one : Nat) (b : Bool) :
    retagCfg ks states symbols (Turing.haltList (cleaner ks states symbols initial) [b]) =
      Turing.haltList (outputCleaner ks states symbols initial output one) [b] := by
  change Cfg.mk none (false,clip states initial,false) _ =
    Cfg.mk none (false,clip states initial,false) _
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The strict numeric Boolean output is read before all core stacks are
cleared; the result then reaches the canonical Boolean halt configuration. -/
theorem read_and_clean (ks states symbols initial output zcode one : Nat)
    (v : Fin (states+1)) (flag : Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) (b : Bool)
    (hdecode : decodeStack (zcode,one,(S (clip ks output)).map Fin.val) = some b)
    (bound : Nat) (hbound : ∀ k, (S k).length ≤ bound) :
    ∃ t ≤ (ks+1)*(bound+1)+2,
      runSteps (outputCleaner ks states symbols initial output one).step t
        (fetchCfg ks states symbols initial output one v flag S) =
          some (Turing.haltList (outputCleaner ks states symbols initial output one) [b]) := by
  obtain ⟨t,ht,hclean⟩ := sweep_all ks states symbols initial b v flag S bound hbound
  have hsim := output_cleaner_run ks states symbols initial output one
    (cfg ks states symbols initial ⟨0,by omega⟩ b v flag S) t
  rw [hclean] at hsim
  change runSteps (outputCleaner ks states symbols initial output one).step t
    (retagCfg ks states symbols (cfg ks states symbols initial ⟨0,by omega⟩ b v flag S)) =
      some (retagCfg ks states symbols (Turing.haltList (cleaner ks states symbols initial) [b])) at hsim
  rw [retag_halt] at hsim
  refine ⟨t+1,by omega,?_⟩
  rw [runSteps_front, fetch_step ks states symbols initial output zcode one v flag S b hdecode]
  exact hsim

set_option backward.isDefEq.respectTransparency false in
/-- A successful numeric run and the separate cleanup program compose as two
proved finite runs. A later combined-machine construction must implement the
handoff to `fetchCfg`; this theorem does not assert that transition. -/
theorem numeric_run_then_cleanup (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (p : Program) (output zcode one : Nat) (bits : List Bool) (fuel : Nat)
    (start r : Shared.Codes.TM2StatementExecution.Result) (b : Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d bits = some start)
    (hrun : run p fuel start = .halted r)
    (he : extractMemory (zcode,one,output,r.label,r.memory) = some b) :
    ∃ n ≤ fuel, ∃ final,
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol).step (2*bits.length+2+n)
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol) bits) = some final ∧ final.l = none ∧
      final.stk (.inl false) = [] ∧ final.stk (.inl true) = [] ∧
      ∃ t ≤ (d.stackCount+1)*(bits.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p + 1)+2,
        runSteps (outputCleaner d.stackCount d.states d.symbols d.initialState output one).step t
          (fetchCfg d.stackCount d.states d.symbols d.initialState output one final.var.2 false
            (fun k => final.stk (.inr k))) =
          some (Turing.haltList (outputCleaner d.stackCount d.states d.symbols d.initialState output one) [b]) := by
  obtain ⟨n,hn,final,hr,hl,hout,hleft,hright,hbound⟩ :=
    Shared.ComplexityBridge.TM2StackBound.combined_numeric_halt_bounded d p output zcode one bits fuel
      start r b hdata hmain hp hstart hrun he
  obtain ⟨t,ht,hclean⟩ := read_and_clean d.stackCount d.states d.symbols d.initialState output zcode one
    final.var.2 false (fun k => final.stk (.inr k)) b hout
      (bits.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p) hbound
  exact ⟨n,hn,final,hr,hl,hleft,hright,t,ht,hclean⟩

/-- Fixture: one output symbol and a second nonempty core stack are decoded
and swept within the stated bound. -/
example :
    let S : Fin 2 → List (Fin 3) := fun k => if k.val = 0 then [0] else [1,0]
    ∃ t ≤ 8, runSteps (outputCleaner 1 1 2 0 0 1).step t
      (fetchCfg 1 1 2 0 0 1 ⟨0,by decide⟩ false S) =
        some (Turing.haltList (outputCleaner 1 1 2 0 0 1) [false]) := by
  let S : Fin 2 → List (Fin 3) := fun k => if k.val = 0 then [0] else [1,0]
  have hdecode : decodeStack (0,1,(S (clip 1 0)).map Fin.val) = some false := by decide
  have hb : ∀ k, (S k).length ≤ 2 := by intro k; fin_cases k <;> decide
  exact read_and_clean 1 1 2 0 0 0 1 ⟨0,by decide⟩ false S false hdecode 2 hb

end Shared.ComplexityBridge.TM2Cleanup
