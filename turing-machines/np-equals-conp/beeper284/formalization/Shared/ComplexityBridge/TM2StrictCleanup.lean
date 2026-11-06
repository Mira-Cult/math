import Shared.ComplexityBridge.TM2PairClock

namespace Shared.ComplexityBridge.TM2StrictCleanup
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2Combined Shared.ComplexityBridge.TM2Cleanup
open Shared.ComplexityBridge.TM2BooleanOutput Shared.ComplexityBridge.TM2FiniteReverse

/-- The default-false interpretation of the existing strict Boolean decoder. -/
def strictAnswer (z one : Nat) (xs : List (Fin (symbols+1))) : Bool :=
  decide (z ≠ one) && ((xs.head?.map (fun a => a.val == one)).getD false) && xs.tail.isEmpty

theorem strictAnswer_eq (symbols z one : Nat) (xs : List (Fin (symbols+1))) :
    strictAnswer z one xs = (decodeStack (z,one,xs.map Fin.val)).getD false := by
  by_cases h : z = one
  · simp [strictAnswer,decodeStack,h]
  · cases xs with
    | nil => simp [strictAnswer,decodeStack,h]
    | cons a xs =>
      cases xs with
      | nil =>
        by_cases ha : a.val = one
        · have haz : a.val ≠ z := by omega
          simp [strictAnswer,decodeStack,h,ha,Ne.symm h]
        · by_cases hz : a.val = z
          · simp [strictAnswer,decodeStack,h,ha,hz]
          · simp [strictAnswer,decodeStack,h,ha,hz]
      | cons c rest => simp [strictAnswer,decodeStack,h]

abbrev Label (ks : Nat) := Bool ⊕ Fin (ks+2)
abbrev State (states : Nat) := Bool × Fin (states+1) × Bool
abbrev SweepStmt (ks states symbols : Nat) :=
  Stmt (TM2Combined.Alphabet ks symbols) (Fin (ks+2)) (State states)

def retag (ks states symbols : Nat) : SweepStmt ks states symbols →
    Stmt (TM2Combined.Alphabet ks symbols) (Label ks) (State states)
  | .push k f q => .push k f (retag ks states symbols q)
  | .peek k f q => .peek k f (retag ks states symbols q)
  | .pop k f q => .pop k f (retag ks states symbols q)
  | .load f q => .load f (retag ks states symbols q)
  | .branch f a b => .branch f (retag ks states symbols a) (retag ks states symbols b)
  | .goto f => .goto (fun v => .inr (f v))
  | .halt => .halt

def embed (ks states symbols : Nat) (c : (cleaner ks states symbols 0).Cfg) :
    Cfg (TM2Combined.Alphabet ks symbols) (Label ks) (State states) :=
  ⟨c.l.map Sum.inr,c.var,c.stk⟩

theorem retag_aux (ks states symbols : Nat) (q : SweepStmt ks states symbols) (v : State states)
    (S : (k : Bool ⊕ Fin (ks+1)) → List (TM2Combined.Alphabet ks symbols k)) :
    stepAux (retag ks states symbols q) v S = embed ks states symbols (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [retag,stepAux,h,iha,ihb]

def program (ks states symbols initial output z one : Nat) : Label ks →
    Stmt (TM2Combined.Alphabet ks symbols) (Label ks) (State states)
  | .inl false => .pop (.inr (clip ks output))
      (fun v h => (decide (z ≠ one) && ((h.map (fun a => a.val == one)).getD false),v.2.1,v.2.2))
      (.goto (fun _ => .inl true))
  | .inl true => .peek (.inr (clip ks output))
      (fun v h => (v.1 && h.isNone,v.2.1,v.2.2))
      (.goto (fun _ => .inr ⟨0,by omega⟩))
  | .inr l => retag ks states symbols (TM2Cleanup.program ks states symbols initial l)

def machine (ks states symbols initial output z one : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := TM2Combined.Alphabet ks symbols
  Λ := Label ks
  main := .inl false
  σ := State states
  initialState := (false,clip states initial,false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols initial output z one

def fetch (ks states symbols initial output z one : Nat) (v : Fin (states+1))
    (S : Fin (ks+1) → List (Fin (symbols+1))) : (machine ks states symbols initial output z one).Cfg :=
  ⟨some (.inl false),(false,v,false),embedStacks ks symbols [] [] S⟩

set_option backward.isDefEq.respectTransparency false in
theorem sweep_step (ks states symbols initial output z one : Nat)
    (c : (cleaner ks states symbols initial).Cfg) :
    (machine ks states symbols initial output z one).step (embed ks states symbols c) =
      ((cleaner ks states symbols initial).step c).map (embed ks states symbols) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (retag ks states symbols (TM2Cleanup.program ks states symbols initial l)) v S) = _
      rw [retag_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem sweep_run (ks states symbols initial output z one : Nat)
    (c : (cleaner ks states symbols initial).Cfg) (n : Nat) :
    runSteps (machine ks states symbols initial output z one).step n (embed ks states symbols c) =
      (runSteps (cleaner ks states symbols initial).step n c).map (embed ks states symbols) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,sweep_step]
    cases h : (cleaner ks states symbols initial).step c with
    | none => rfl
    | some c' => exact ih c'

theorem fetch_first (ks states symbols initial output z one : Nat) (v : Fin (states+1))
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols initial output z one).step (fetch ks states symbols initial output z one v S) =
      some ⟨some (.inl true),
        (decide (z ≠ one) && (((S (clip ks output)).head?.map (fun a => a.val == one)).getD false),v,false),
        embedStacks ks symbols [] [] (Function.update S (clip ks output) (S (clip ks output)).tail)⟩ := by
  change some (Cfg.mk (some (Sum.inl true : Label ks)) _
    (Function.update (embedStacks ks symbols [] [] S) (.inr (clip ks output)) (S (clip ks output)).tail)) = _
  rw [← embedStacks_update]
  rfl

theorem fetch_second (ks states symbols initial output z one : Nat) (v : Fin (states+1))
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols initial output z one).step
      ⟨some (.inl true),
        (decide (z ≠ one) && (((S (clip ks output)).head?.map (fun a => a.val == one)).getD false),v,false),
        embedStacks ks symbols [] [] (Function.update S (clip ks output) (S (clip ks output)).tail)⟩ =
      some (embed ks states symbols (cfg ks states symbols initial ⟨0,by omega⟩
        (strictAnswer z one (S (clip ks output))) v false
        (Function.update S (clip ks output) (S (clip ks output)).tail))) := by
  change some (Cfg.mk (some (Sum.inr (⟨0,by omega⟩ : Fin (ks+2)) : Label ks))
    ((decide (z ≠ one) && (((S (clip ks output)).head?.map (fun a => a.val == one)).getD false)) &&
      ((Function.update S (clip ks output) (S (clip ks output)).tail) (clip ks output)).head?.isNone,v,false) _) = _
  simp only [Function.update_self]
  have h : (S (clip ks output)).tail.head?.isNone = (S (clip ks output)).tail.isEmpty := by
    cases (S (clip ks output)).tail <;> rfl
  rw [h]
  rfl

theorem embed_halt (ks states symbols initial output z one : Nat) (answer : Bool) :
    embed ks states symbols (Turing.haltList (cleaner ks states symbols initial) [answer]) =
      Turing.haltList (machine ks states symbols initial output z one) [answer] := by
  change Cfg.mk none (false,clip states initial,false) _ = Cfg.mk none (false,clip states initial,false) _
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Strictly decode every possible output stack. Invalid, empty, multi-symbol,
and duplicate-code outputs all yield false; no validity assumption is needed. -/
theorem strict_read_and_clean (ks states symbols initial output z one : Nat)
    (v : Fin (states+1)) (S : Fin (ks+1) → List (Fin (symbols+1)))
    (bound : Nat) (hbound : ∀ j, (S j).length ≤ bound) :
    ∃ t ≤ (ks+1)*(bound+1)+3,
      runSteps (machine ks states symbols initial output z one).step t
        (fetch ks states symbols initial output z one v S) =
      some (Turing.haltList (machine ks states symbols initial output z one)
        [(decodeStack (z,one,(S (clip ks output)).map Fin.val)).getD false]) := by
  let j := clip ks output
  let S' := Function.update S j (S j).tail
  have hb : ∀ i, (S' i).length ≤ bound := by
    intro i
    by_cases hi : i = j
    · subst i
      simp only [S', Function.update_self, List.length_tail]
      have h := hbound j
      omega
    · simpa [S',Function.update_of_ne hi] using hbound i
  let answer := strictAnswer z one (S j)
  obtain ⟨t,ht,hclean⟩ := sweep_all ks states symbols initial answer v false S' bound hb
  have hsim := sweep_run ks states symbols initial output z one (cfg ks states symbols initial ⟨0,by omega⟩ answer v false S') t
  rw [hclean] at hsim
  change runSteps (machine ks states symbols initial output z one).step t
    (embed ks states symbols (cfg ks states symbols initial ⟨0,by omega⟩ answer v false S')) =
      some (embed ks states symbols (Turing.haltList (cleaner ks states symbols initial) [answer])) at hsim
  rw [embed_halt ks states symbols initial output z one] at hsim
  refine ⟨t+2,by omega,?_⟩
  have hn : t+2 = (t+1)+1 := by omega
  rw [hn,runSteps_front,fetch_first]
  change runSteps (machine ks states symbols initial output z one).step (t+1)
    ⟨some (.inl true),
      (decide (z ≠ one) && (((S j).head?.map (fun a => a.val == one)).getD false),v,false),
      embedStacks ks symbols [] [] S'⟩ = _
  rw [runSteps_front,fetch_second]
  change runSteps (machine ks states symbols initial output z one).step t
    (embed ks states symbols (cfg ks states symbols initial ⟨0,by omega⟩ answer v false S')) = _
  have ha : answer = (decodeStack (z,one,(S j).map Fin.val)).getD false := strictAnswer_eq symbols z one (S j)
  rw [← ha]
  exact hsim

example : strictAnswer 0 1 ([1,0] : List (Fin 3)) = false := by decide
example : strictAnswer 0 0 ([0] : List (Fin 3)) = false := by decide
example : strictAnswer 0 1 ([1] : List (Fin 3)) = true := by decide
example : strictAnswer 0 1 ([] : List (Fin 3)) = false := by decide

/-- Actual machine trace: a multi-symbol output beginning with the true code
is rejected, rather than accepted from its head alone. -/
example : (runSteps (machine 0 1 2 0 0 0 1).step 5
    (fetch 0 1 2 0 0 0 1 ⟨0,by decide⟩ (fun _ => [1,0]))).map
      (fun c => c.stk (.inl true)) = some [false] := by
  change (Option.map (fun c => c.stk (.inl true)) (runSteps (machine 0 1 2 0 0 0 1).step 5
    (fetch 0 1 2 0 0 0 1 ⟨0,by decide⟩ (fun _ => [1,0]))) : Option (List Bool)) = some [false]
  decide

example : (runSteps (machine 0 1 2 0 0 0 1).step 4
    (fetch 0 1 2 0 0 0 1 ⟨0,by decide⟩ (fun _ => [1]))).map
      (fun c => c.stk (.inl true)) = some [true] := by
  change (Option.map (fun c => c.stk (.inl true)) (runSteps (machine 0 1 2 0 0 0 1).step 4
    (fetch 0 1 2 0 0 0 1 ⟨0,by decide⟩ (fun _ => [1]))) : Option (List Bool)) = some [true]
  decide

end Shared.ComplexityBridge.TM2StrictCleanup
