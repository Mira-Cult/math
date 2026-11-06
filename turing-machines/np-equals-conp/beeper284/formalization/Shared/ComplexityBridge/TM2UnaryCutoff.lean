import Shared.ComplexityBridge.TM2VerifierValidity

namespace Shared.ComplexityBridge.TM2UnaryCutoff
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | witness | cutoff
  deriving DecidableEq
inductive Label where | compare | accept | reject
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.witness,.cutoff] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.compare,.accept,.reject] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label Bool
  | .compare => .pop .witness (fun _ h => h.isSome)
      (.branch id
        (.pop .cutoff (fun _ h => h.isSome)
          (.branch id (.goto (fun _ => .compare)) (.goto (fun _ => .reject))))
        (.goto (fun _ => .accept)))
  | .accept => .goto (fun _ => .accept)
  | .reject => .goto (fun _ => .reject)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .witness
  k₁ := .cutoff
  Γ := fun _ => Bool
  Λ := Label
  main := .compare
  σ := Bool
  initialState := false
  m := program

def stackVals (w c : Nat) : Stack → List Bool
  | .witness => List.replicate w true
  | .cutoff => List.replicate c true

def cfg (l : Label) (flag : Bool) (w c : Nat) : machine.Cfg :=
  ⟨some l,flag,stackVals w c⟩

theorem step_both (flag : Bool) (w c : Nat) :
    machine.step (cfg .compare flag (w+1) (c+1)) = some (cfg .compare true w c) := by
  change some (Cfg.mk (some Label.compare) true
    (Function.update (Function.update (stackVals (w+1) (c+1)) .witness (List.replicate w true))
      .cutoff (List.replicate c true))) = some (Cfg.mk (some Label.compare) true (stackVals w c))
  congr 1; congr 1; funext s; cases s <;> simp [stackVals,Function.update]

theorem step_accept (flag : Bool) (c : Nat) :
    machine.step (cfg .compare flag 0 c) = some (cfg .accept false 0 c) := by
  change some (Cfg.mk (some Label.accept) false (Function.update (stackVals 0 c) .witness [])) =
    some (Cfg.mk (some Label.accept) false (stackVals 0 c))
  congr 1; congr 1; funext s; cases s <;> simp [stackVals,Function.update]

theorem step_reject (flag : Bool) (w : Nat) :
    machine.step (cfg .compare flag (w+1) 0) = some (cfg .reject false w 0) := by
  change some (Cfg.mk (some Label.reject) false
    (Function.update (Function.update (stackVals (w+1) 0) .witness (List.replicate w true)) .cutoff [])) =
      some (Cfg.mk (some Label.reject) false (stackVals w 0))
  congr 1; congr 1; funext s; cases s <;> simp [stackVals,Function.update]

/-- With a sufficiently large original cutoff, the comparator accepts after
one block per witness bit and one final empty-witness test. -/
theorem accept_run (w c : Nat) (flag : Bool) (h : w ≤ c) :
    runSteps machine.step (w+1) (cfg .compare flag w c) = some (cfg .accept false 0 (c-w)) := by
  induction w generalizing c flag with
  | zero =>
    simp only [Nat.zero_add,Nat.sub_zero]
    change machine.step (cfg .compare flag 0 c) = _
    exact step_accept flag c
  | succ w ih =>
    cases c with
    | zero => omega
    | succ c =>
      have hc : w ≤ c := by omega
      rw [show w+1+1 = (w+1)+1 by omega, runSteps_front, step_both]
      simpa using ih c true hc

/-- An oversized witness is rejected immediately after consuming the first
bit for which no cutoff tick remains. -/
theorem reject_run (w c : Nat) (flag : Bool) (h : c < w) :
    runSteps machine.step (c+1) (cfg .compare flag w c) = some (cfg .reject false (w-(c+1)) 0) := by
  induction c generalizing w flag with
  | zero =>
    cases w with
    | zero => omega
    | succ w =>
      simp only [Nat.zero_add,Nat.add_sub_cancel_right]
      change machine.step (cfg .compare flag (w+1) 0) = _
      exact step_reject flag w
  | succ c ih =>
    cases w with
    | zero => omega
    | succ w =>
      have hw : c < w := by omega
      rw [show c+1+1 = (c+1)+1 by omega,runSteps_front,step_both]
      simpa using ih w true hw

/-- Both paths terminate within `w+1` blocks and select the exact original
cutoff comparison; the unary stacks here are explicitly preloaded. -/
theorem compare_progress (w c : Nat) :
    ∃ n ≤ w+1, ∃ remaining,
      runSteps machine.step n (cfg .compare false w c) =
        some (if w ≤ c then cfg .accept false 0 remaining else cfg .reject false remaining 0) := by
  by_cases h : w ≤ c
  · exact ⟨w+1,by omega,c-w,by simpa [h] using accept_run w c false h⟩
  · have hc : c < w := by omega
    exact ⟨c+1,by omega,w-(c+1),by simpa [h] using reject_run w c false hc⟩

/-- Instantiation to the retained verifier cutoff, not the enlarged outer
search exponent. Computing the cutoff ticks is a separate obligation. -/
theorem verifier_cutoff_progress (v : Shared.NPCONP.TM2Verifier.Verifier) (x w : List Bool) :
    ∃ n ≤ w.length+1, ∃ remaining,
      runSteps machine.step n
        (cfg .compare false w.length (Shared.NPCONP.TM2Verifier.cutoff v x)) =
        some (if w.length ≤ Shared.NPCONP.TM2Verifier.cutoff v x then cfg .accept false 0 remaining
          else cfg .reject false remaining 0) := compare_progress _ _

/-- A passing comparison leaves the verifier's checker unchanged. -/
theorem verifier_accept (v : Shared.NPCONP.TM2Verifier.Verifier) (x w : List Bool)
    (h : w.length ≤ Shared.NPCONP.TM2Verifier.cutoff v x) :
    runSteps machine.step (w.length+1)
      (cfg .compare false w.length (Shared.NPCONP.TM2Verifier.cutoff v x)) =
        some (cfg .accept false 0 (Shared.NPCONP.TM2Verifier.cutoff v x-w.length)) ∧
    Shared.NPCONP.TM2Verifier.verify v x w = Shared.Codes.TM2PairCandidate.evaluate v.2 x w := by
  exact ⟨accept_run _ _ false h, by simp [Shared.NPCONP.TM2Verifier.verify,h]⟩

/-- A failing comparison gives the verifier's prescribed false result, even
if a larger outer witness bound admits this witness. -/
theorem verifier_reject (v : Shared.NPCONP.TM2Verifier.Verifier) (x w : List Bool)
    (h : Shared.NPCONP.TM2Verifier.cutoff v x < w.length) :
    runSteps machine.step (Shared.NPCONP.TM2Verifier.cutoff v x+1)
      (cfg .compare false w.length (Shared.NPCONP.TM2Verifier.cutoff v x)) =
        some (cfg .reject false (w.length-(Shared.NPCONP.TM2Verifier.cutoff v x+1)) 0) ∧
    Shared.NPCONP.TM2Verifier.verify v x w = some false := by
  exact ⟨reject_run _ _ false h, Shared.NPCONP.TM2Verifier.cutoff_rejects v x w h⟩

example : (runSteps machine.step 3 (cfg .compare false 2 2)).map
    (fun c => match c.l with | some .accept => true | _ => false) = some true := by
  change (Option.map (fun c => match c.l with | some .accept => true | _ => false)
    (runSteps machine.step 3 (cfg .compare false 2 2)) : Option Bool) = some true
  decide
example : (runSteps machine.step 3 (cfg .compare false 3 2)).map
    (fun c => match c.l with | some .reject => true | _ => false) = some true := by
  change (Option.map (fun c => match c.l with | some .reject => true | _ => false)
    (runSteps machine.step 3 (cfg .compare false 3 2)) : Option Bool) = some true
  decide
example : (runSteps machine.step 1 (cfg .compare false 0 0)).map
    (fun c => match c.l with | some .accept => true | _ => false) = some true := by
  change (Option.map (fun c => match c.l with | some .accept => true | _ => false)
    (runSteps machine.step 1 (cfg .compare false 0 0)) : Option Bool) = some true
  decide

end Shared.ComplexityBridge.TM2UnaryCutoff
