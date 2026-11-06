import Shared.ComplexityBridge.TM2UnaryMultiply

namespace Shared.ComplexityBridge.TM2UnaryTransfer
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2UnaryMultiply (Stack stackVals)

/-- A source that is stable once it reaches a terminal state remains there. -/
theorem run_stable {α : Type} (step : α → Option α) (terminal : α → Prop)
    (stable : ∀ c, terminal c → step c = some c) (c : α) (hc : terminal c) :
    ∀ n, runSteps step n c = some c := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front, stable c hc]
    exact ih

/-- Lift a finite run to a target that agrees before a stable source terminal.
The target may dispatch on the terminal state; it need only reach the same
terminal image in at most the source's original number of steps. -/
theorem run_to_stable_lift {α β : Type} (source : α → Option α) (target : β → Option β)
    (embed : α → β) (terminal : α → Prop) [DecidablePred terminal]
    (stable : ∀ c, terminal c → source c = some c)
    (simulate : ∀ c, ¬ terminal c → target (embed c) = (source c).map embed)
    (n : Nat) (start finish : α) (hfinish : terminal finish)
    (hrun : runSteps source n start = some finish) :
    ∃ m ≤ n, runSteps target m (embed start) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
    change some start = some finish at hrun
    cases hrun
    exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ n ih =>
    by_cases hs : terminal start
    · have he : start = finish := by
        have ht := run_stable source terminal stable start hs (n+1)
        rw [hrun] at ht
        exact Option.some.inj ht.symm
      subst finish
      exact ⟨0, Nat.zero_le _, rfl⟩
    · rw [runSteps_front] at hrun
      cases hstep : source start with
      | none => simp [hstep] at hrun
      | some next =>
        have hrest : runSteps source n next = some finish := by simpa [hstep] using hrun
        obtain ⟨m, hm, htarget⟩ := ih next hrest
        refine ⟨m+1, by omega, ?_⟩
        rw [runSteps_front, simulate start hs, hstep]
        simpa using htarget

/-- Clearing the old first operand and transferring the product to it is a
finite-control operation. The second operand and temporary stacks are untouched. -/
inductive Label where
  | clear | transfer | ready
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.clear, .transfer, .ready] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label Bool
  | .clear => .pop .a (fun _ h => h.isSome)
      (.branch id (.goto (fun _ => .clear)) (.goto (fun _ => .transfer)))
  | .transfer => .pop .output (fun _ h => h.isSome)
      (.branch id (.push .a (fun _ => true) (.goto (fun _ => .transfer)))
        (.goto (fun _ => .ready)))
  | .ready => .goto (fun _ => .ready)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .a
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .clear
  σ := Bool
  initialState := false
  m := program

def cfg (l : Label) (flag : Bool) (a b ta bt out : Nat) : machine.Cfg :=
  ⟨some l, flag, stackVals a b ta bt out⟩

theorem clear_cons (flag : Bool) (a b ta bt out : Nat) :
    machine.step (cfg .clear flag (a+1) b ta bt out) = some (cfg .clear true a b ta bt out) := by
  change some (Cfg.mk (some Label.clear) true
    (Function.update (stackVals (a+1) b ta bt out) .a (List.replicate a true))) =
      some (Cfg.mk (some Label.clear) true (stackVals a b ta bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals, Function.update]

theorem clear_nil (flag : Bool) (b ta bt out : Nat) :
    machine.step (cfg .clear flag 0 b ta bt out) = some (cfg .transfer false 0 b ta bt out) := by
  change some (Cfg.mk (some Label.transfer) false
    (Function.update (stackVals 0 b ta bt out) .a [])) =
      some (Cfg.mk (some Label.transfer) false (stackVals 0 b ta bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals, Function.update]

theorem transfer_cons (flag : Bool) (a b ta bt out : Nat) :
    machine.step (cfg .transfer flag a b ta bt (out+1)) =
      some (cfg .transfer true (a+1) b ta bt out) := by
  change some (Cfg.mk (some Label.transfer) true
    (Function.update (Function.update (stackVals a b ta bt (out+1)) .output
      (List.replicate out true)) .a (true :: List.replicate a true))) =
      some (Cfg.mk (some Label.transfer) true (stackVals (a+1) b ta bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals, Function.update, List.replicate_succ]

theorem transfer_nil (flag : Bool) (a b ta bt : Nat) :
    machine.step (cfg .transfer flag a b ta bt 0) = some (cfg .ready false a b ta bt 0) := by
  change some (Cfg.mk (some Label.ready) false
    (Function.update (stackVals a b ta bt 0) .output [])) =
      some (Cfg.mk (some Label.ready) false (stackVals a b ta bt 0))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals, Function.update]

theorem clear_run (a : Nat) (flag : Bool) (b ta bt out : Nat) :
    ∃ f, runSteps machine.step a (cfg .clear flag a b ta bt out) =
      some (cfg .clear f 0 b ta bt out) := by
  induction a generalizing flag with
  | zero => exact ⟨flag, by simp [runSteps]⟩
  | succ a ih =>
    obtain ⟨f, h⟩ := ih true
    refine ⟨f, ?_⟩
    rw [runSteps_front, clear_cons]
    exact h

theorem transfer_run (out : Nat) (flag : Bool) (a b ta bt : Nat) :
    ∃ f, runSteps machine.step out (cfg .transfer flag a b ta bt out) =
      some (cfg .transfer f (a+out) b ta bt 0) := by
  induction out generalizing flag a with
  | zero => exact ⟨flag, by simp [runSteps]⟩
  | succ out ih =>
    obtain ⟨f, h⟩ := ih true (a+1)
    refine ⟨f, ?_⟩
    rw [runSteps_front, transfer_cons]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The old first operand is discarded, the output becomes the new first
operand, and all other stacks are preserved. Two empty-stack tests are charged. -/
theorem reset_and_transfer (a b ta bt out : Nat) :
    runSteps machine.step (a+out+2) (cfg .clear false a b ta bt out) =
      some (cfg .ready false out b ta bt 0) := by
  obtain ⟨f, hc⟩ := clear_run a false b ta bt out
  have hc' : runSteps machine.step (a+1) (cfg .clear false a b ta bt out) =
      some (cfg .transfer false 0 b ta bt out) := by
    rw [runSteps_add, hc]
    change machine.step (cfg .clear f 0 b ta bt out) = _
    exact clear_nil f b ta bt out
  obtain ⟨g, ht⟩ := transfer_run out false 0 b ta bt
  simp only [Nat.zero_add] at ht
  have ht' : runSteps machine.step (out+1) (cfg .transfer false 0 b ta bt out) =
      some (cfg .ready false out b ta bt 0) := by
    rw [runSteps_add, ht]
    change machine.step (cfg .transfer g out b ta bt 0) = _
    exact transfer_nil g out b ta bt
  have hn : a+out+2 = (a+1)+(out+1) := by omega
  rw [hn, runSteps_add, hc']
  exact ht'

example : (runSteps machine.step 7 (cfg .clear false 2 3 0 0 3)).map
    (fun c => c.stk .a) = some (List.replicate 3 true) := by
  change (Option.map (fun c => c.stk .a) (runSteps machine.step 7 (cfg .clear false 2 3 0 0 3)) :
    Option (List Bool)) = some (List.replicate 3 true)
  decide

end Shared.ComplexityBridge.TM2UnaryTransfer
