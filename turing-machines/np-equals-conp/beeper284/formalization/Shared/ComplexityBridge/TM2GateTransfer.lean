import Shared.ComplexityBridge.TM2GateClean

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2GateTransfer
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev GateKey := Shared.ComplexityBridge.TM2CutoffGate.Key
abbrev Key (tm : Turing.FinTM2) := GateKey ⊕ tm.K

def Alphabet (tm : Turing.FinTM2) : Key tm → Type
  | .inl _ => Bool
  | .inr k => tm.Γ k

inductive Label where | load | restore | discard | ready | rejected
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.load,.restore,.discard,.ready,.rejected] (by intro l; cases l <;> simp)

def program (tm : Turing.FinTM2) (input : tm.Γ tm.k₀ ≃ Bool) :
    Label → Stmt (Alphabet tm) Label (Option Bool)
  | .load => .pop (.inl (.inl false)) (fun _ h => h)
      (.branch Option.isSome
        (.push (.inl (.inl true)) (fun v => v.getD false) (.goto (fun _ => .load)))
        (.goto (fun _ => .restore)))
  | .restore => .pop (.inl (.inl true)) (fun _ h => h)
      (.branch Option.isSome
        (.push (.inr tm.k₀) (fun v => input.symm (v.getD false)) (.goto (fun _ => .restore)))
        (.goto (fun _ => .ready)))
  | .discard => .pop (.inl (.inl false)) (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .discard)) (.goto (fun _ => .rejected)))
  | .ready => .goto (fun _ => .ready)
  | .rejected => .goto (fun _ => .rejected)

def machine (tm : Turing.FinTM2) (input : tm.Γ tm.k₀ ≃ Bool) : Turing.FinTM2 := by
  letI := tm.kFin
  exact {
    K := Key tm
    k₀ := .inl (.inl false)
    k₁ := .inr tm.k₁
    Γ := Alphabet tm
    Λ := Label
    main := .load
    σ := Option Bool
    initialState := none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := program tm input }

def gateStacks (input scratch : List Bool) : GateKey → List Bool
  | .inl false => input
  | .inl true => scratch
  | .inr _ => []

def stackVals (tm : Turing.FinTM2) (input scratch : List Bool) (S : (k : tm.K) → List (tm.Γ k)) :
    (k : Key tm) → List (Alphabet tm k)
  | .inl k => gateStacks input scratch k
  | .inr k => S k

def cfg (tm : Turing.FinTM2) (inputAlphabet : tm.Γ tm.k₀ ≃ Bool) (l : Label) (v : Option Bool)
    (input scratch : List Bool) (S : (k : tm.K) → List (tm.Γ k)) : (machine tm inputAlphabet).Cfg :=
  ⟨some l,v,stackVals tm input scratch S⟩

theorem gateStacks_update_input (input scratch xs : List Bool) :
    Function.update (gateStacks input scratch) (.inl false) xs = gateStacks xs scratch := by
  funext k
  cases k with
  | inl b => cases b <;> simp [gateStacks,Function.update]
  | inr k => simp [gateStacks,Function.update]

theorem gateStacks_update_scratch (input scratch xs : List Bool) :
    Function.update (gateStacks input scratch) (.inl true) xs = gateStacks input xs := by
  funext k
  cases k with
  | inl b => cases b <;> simp [gateStacks,Function.update]
  | inr k => simp [gateStacks,Function.update]

set_option backward.isDefEq.respectTransparency false in
theorem stackVals_update_gate (tm : Turing.FinTM2) (input scratch : List Bool)
    (S : (k : tm.K) → List (tm.Γ k)) (j : GateKey) (xs : List Bool) :
    Function.update (stackVals tm input scratch S) (.inl j) xs =
      (fun k => match k with | .inl q => (Function.update (gateStacks input scratch) j xs) q | .inr q => S q) := by
  funext k
  cases k with
  | inl q =>
    by_cases h : q = j
    · subst q; simp [stackVals]
    · have hh : (Sum.inl q : Key tm) ≠ .inl j := by simpa using h
      simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]
  | inr q => simp [stackVals,Function.update]

set_option backward.isDefEq.respectTransparency false in
theorem stackVals_update_checker (tm : Turing.FinTM2) (input scratch : List Bool)
    (S : (k : tm.K) → List (tm.Γ k)) (j : tm.K) (xs : List (tm.Γ j)) :
    Function.update (stackVals tm input scratch S) (.inr j) xs =
      stackVals tm input scratch (Function.update S j xs) := by
  funext k
  cases k with
  | inl q => simp [stackVals,Function.update]
  | inr q =>
    by_cases h : q = j
    · subst q; simp [stackVals]
    · have hh : (Sum.inr q : Key tm) ≠ .inr j := by simpa using h
      simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]

theorem initStacks_push (tm : Turing.FinTM2) (a : tm.Γ tm.k₀) (xs : List (tm.Γ tm.k₀)) :
    Function.update (Turing.initList tm xs).stk tm.k₀ (a::xs) = (Turing.initList tm (a::xs)).stk := by
  funext k
  by_cases h : k = tm.k₀
  · subst k; simp [Turing.initList]
  · simp [Turing.initList,h,Function.update_of_ne h]

set_option backward.isDefEq.respectTransparency false in
theorem load_cons (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (v : Option Bool)
    (b : Bool) (xs scratch : List Bool) (S : (k : tm.K) → List (tm.Γ k)) :
    (machine tm ea).step (cfg tm ea .load v (b::xs) scratch S) =
      some (cfg tm ea .load (some b) xs (b::scratch) S) := by
  change some (Cfg.mk (some Label.load) (some b)
    (Function.update (Function.update (stackVals tm (b::xs) scratch S) (.inl (.inl false)) xs)
      (.inl (.inl true)) (b::scratch))) = some (Cfg.mk _ _ _)
  congr 1
  congr 1
  rw [stackVals_update_gate,gateStacks_update_input]
  change Function.update (stackVals tm xs scratch S) (.inl (.inl true)) (b::scratch) = _
  rw [stackVals_update_gate,gateStacks_update_scratch]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem load_nil (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (v : Option Bool)
    (scratch : List Bool) (S : (k : tm.K) → List (tm.Γ k)) :
    (machine tm ea).step (cfg tm ea .load v [] scratch S) = some (cfg tm ea .restore none [] scratch S) := by
  change some (Cfg.mk (some Label.restore) none
    (Function.update (stackVals tm [] scratch S) (.inl (.inl false)) [])) = some (Cfg.mk _ _ _)
  congr 1
  congr 1
  rw [stackVals_update_gate,gateStacks_update_input]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem restore_cons (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (v : Option Bool)
    (b : Bool) (xs : List Bool) (ys : List (tm.Γ tm.k₀)) :
    (machine tm ea).step (cfg tm ea .restore v [] (b::xs) (Turing.initList tm ys).stk) =
      some (cfg tm ea .restore (some b) [] xs (Turing.initList tm (ea.symm b::ys)).stk) := by
  change some (Cfg.mk (some Label.restore) (some b)
    (Function.update (Function.update (stackVals tm [] (b::xs) (Turing.initList tm ys).stk)
      (.inl (.inl true)) xs) (.inr tm.k₀) (ea.symm b::(Turing.initList tm ys).stk tm.k₀))) = some (Cfg.mk _ _ _)
  have hinit : (Turing.initList tm ys).stk tm.k₀ = ys := by simp [Turing.initList]
  rw [hinit]
  congr 1
  congr 1
  rw [stackVals_update_gate,gateStacks_update_scratch]
  change Function.update (stackVals tm [] xs (Turing.initList tm ys).stk) (.inr tm.k₀) (ea.symm b::ys) = _
  rw [stackVals_update_checker,initStacks_push]

set_option backward.isDefEq.respectTransparency false in
theorem restore_nil (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (v : Option Bool)
    (ys : List (tm.Γ tm.k₀)) :
    (machine tm ea).step (cfg tm ea .restore v [] [] (Turing.initList tm ys).stk) =
      some (cfg tm ea .ready none [] [] (Turing.initList tm ys).stk) := by
  change some (Cfg.mk (some Label.ready) none
    (Function.update (stackVals tm [] [] (Turing.initList tm ys).stk) (.inl (.inl true)) [])) = some (Cfg.mk _ _ _)
  congr 1
  congr 1
  rw [stackVals_update_gate,gateStacks_update_scratch]
  rfl

theorem load_run (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (xs scratch : List Bool)
    (S : (k : tm.K) → List (tm.Γ k)) (v : Option Bool) :
    ∃ v', runSteps (machine tm ea).step xs.length (cfg tm ea .load v xs scratch S) =
      some (cfg tm ea .load v' [] (xs.reverse++scratch) S) := by
  induction xs generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b xs ih =>
    obtain ⟨v',h⟩ := ih (b::scratch) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,load_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore_run (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (xs : List Bool)
    (ys : List (tm.Γ tm.k₀)) (v : Option Bool) :
    ∃ v', runSteps (machine tm ea).step xs.length (cfg tm ea .restore v [] xs (Turing.initList tm ys).stk) =
      some (cfg tm ea .restore v' [] [] (Turing.initList tm (xs.reverse.map ea.symm ++ ys)).stk) := by
  induction xs generalizing ys v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b xs ih =>
    obtain ⟨v',h⟩ := ih (ea.symm b::ys) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- A real two-pass transfer preserves the encoded input order and initializes
exactly the supplied checker's input stack; both gate stacks become empty. -/
theorem transfer_correct (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (bits : List Bool) :
    runSteps (machine tm ea).step (2*bits.length+2)
      (cfg tm ea .load none bits [] (Turing.initList tm []).stk) =
      some (cfg tm ea .ready none [] [] (Turing.initList tm (bits.map ea.symm)).stk) := by
  obtain ⟨v,hload⟩ := load_run tm ea bits [] (Turing.initList tm []).stk none
  simp only [List.append_nil] at hload
  obtain ⟨u,hrestore⟩ := restore_run tm ea bits.reverse [] none
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hrestore
  have ht : 2*bits.length+2 = bits.length+(1+(bits.length+1)) := by omega
  rw [ht,runSteps_add,hload]
  change runSteps (machine tm ea).step (1+(bits.length+1))
    (cfg tm ea .load v [] bits.reverse (Turing.initList tm []).stk) = _
  rw [show 1+(bits.length+1) = (bits.length+1)+1 by omega,runSteps_front,load_nil]
  change runSteps (machine tm ea).step (bits.length+1)
    (cfg tm ea .restore none [] bits.reverse (Turing.initList tm []).stk) = _
  rw [runSteps_add,hrestore]
  exact restore_nil tm ea u _

set_option backward.isDefEq.respectTransparency false in
theorem discard_cons (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (v : Option Bool)
    (b : Bool) (xs scratch : List Bool) (S : (k : tm.K) → List (tm.Γ k)) :
    (machine tm ea).step (cfg tm ea .discard v (b::xs) scratch S) =
      some (cfg tm ea .discard (some b) xs scratch S) := by
  change some (Cfg.mk (some Label.discard) (some b)
    (Function.update (stackVals tm (b::xs) scratch S) (.inl (.inl false)) xs)) = some (Cfg.mk _ _ _)
  congr 1
  congr 1
  rw [stackVals_update_gate,gateStacks_update_input]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem discard_nil (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (v : Option Bool)
    (scratch : List Bool) (S : (k : tm.K) → List (tm.Γ k)) :
    (machine tm ea).step (cfg tm ea .discard v [] scratch S) =
      some (cfg tm ea .rejected none [] scratch S) := by
  change some (Cfg.mk (some Label.rejected) none
    (Function.update (stackVals tm [] scratch S) (.inl (.inl false)) [])) = some (Cfg.mk _ _ _)
  congr 1
  congr 1
  rw [stackVals_update_gate,gateStacks_update_input]
  rfl

/-- The reject path clears the encoded input without touching the checker. -/
theorem discard_run (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (bits scratch : List Bool)
    (S : (k : tm.K) → List (tm.Γ k)) (v : Option Bool) :
    runSteps (machine tm ea).step (bits.length+1) (cfg tm ea .discard v bits scratch S) =
      some (cfg tm ea .rejected none [] scratch S) := by
  induction bits generalizing v with
  | nil => exact discard_nil tm ea v scratch S
  | cons b bits ih =>
    rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,discard_cons]
    exact ih (some b)

end Shared.ComplexityBridge.TM2GateTransfer
