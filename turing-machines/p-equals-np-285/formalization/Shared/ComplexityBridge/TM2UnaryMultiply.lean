import Shared.ComplexityBridge.TM2UnaryClock

namespace Shared.ComplexityBridge.TM2UnaryMultiply
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where
  | a | b | aTmp | bTmp | output
  deriving DecidableEq
inductive Label where
  | outer | inner | restoreB | restoreA | done
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.a,.b,.aTmp,.bTmp,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.outer,.inner,.restoreB,.restoreA,.done] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label Bool
  | .outer => .pop .a (fun _ h => h.isSome)
      (.branch id (.push .aTmp (fun _ => true) (.goto (fun _ => .inner))) (.goto (fun _ => .restoreA)))
  | .inner => .pop .b (fun _ h => h.isSome)
      (.branch id (.push .bTmp (fun _ => true) (.push .output (fun _ => true) (.goto (fun _ => .inner))))
        (.goto (fun _ => .restoreB)))
  | .restoreB => .pop .bTmp (fun _ h => h.isSome)
      (.branch id (.push .b (fun _ => true) (.goto (fun _ => .restoreB))) (.goto (fun _ => .outer)))
  | .restoreA => .pop .aTmp (fun _ h => h.isSome)
      (.branch id (.push .a (fun _ => true) (.goto (fun _ => .restoreA))) (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)

def multiplier : Turing.FinTM2 where
  K := Stack
  k₀ := .a
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .outer
  σ := Bool
  initialState := false
  m := program

def stackVals (a b ta bt out : Nat) : Stack → List Bool
  | .a => List.replicate a true
  | .b => List.replicate b true
  | .aTmp => List.replicate ta true
  | .bTmp => List.replicate bt true
  | .output => List.replicate out true

def cfg (l : Label) (flag : Bool) (a b ta bt out : Nat) : multiplier.Cfg :=
  ⟨some l,flag,stackVals a b ta bt out⟩

theorem outer_cons (flag : Bool) (a b ta bt out : Nat) :
    multiplier.step (cfg .outer flag (a+1) b ta bt out) = some (cfg .inner true a b (ta+1) bt out) := by
  change some (Cfg.mk (some Label.inner) true
    (Function.update (Function.update (stackVals (a+1) b ta bt out) .a (List.replicate a true)) .aTmp (true::List.replicate ta true))) =
      some (Cfg.mk (some Label.inner) true (stackVals a b (ta+1) bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals,Function.update,List.replicate_succ]

theorem outer_nil (flag : Bool) (b ta bt out : Nat) :
    multiplier.step (cfg .outer flag 0 b ta bt out) = some (cfg .restoreA false 0 b ta bt out) := by
  change some (Cfg.mk (some Label.restoreA) false (Function.update (stackVals 0 b ta bt out) .a [])) =
    some (Cfg.mk (some Label.restoreA) false (stackVals 0 b ta bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals,Function.update]

theorem inner_cons (flag : Bool) (a b ta bt out : Nat) :
    multiplier.step (cfg .inner flag a (b+1) ta bt out) = some (cfg .inner true a b ta (bt+1) (out+1)) := by
  change some (Cfg.mk (some Label.inner) true
    (Function.update (Function.update (Function.update (stackVals a (b+1) ta bt out) .b (List.replicate b true))
      .bTmp (true::List.replicate bt true)) .output (true::List.replicate out true))) =
        some (Cfg.mk (some Label.inner) true (stackVals a b ta (bt+1) (out+1)))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals,Function.update,List.replicate_succ]

theorem inner_nil (flag : Bool) (a ta bt out : Nat) :
    multiplier.step (cfg .inner flag a 0 ta bt out) = some (cfg .restoreB false a 0 ta bt out) := by
  change some (Cfg.mk (some Label.restoreB) false (Function.update (stackVals a 0 ta bt out) .b [])) =
    some (Cfg.mk (some Label.restoreB) false (stackVals a 0 ta bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals,Function.update]

theorem restoreB_cons (flag : Bool) (a b ta bt out : Nat) :
    multiplier.step (cfg .restoreB flag a b ta (bt+1) out) = some (cfg .restoreB true a (b+1) ta bt out) := by
  change some (Cfg.mk (some Label.restoreB) true
    (Function.update (Function.update (stackVals a b ta (bt+1) out) .bTmp (List.replicate bt true))
      .b (true::List.replicate b true))) =
        some (Cfg.mk (some Label.restoreB) true (stackVals a (b+1) ta bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals,Function.update,List.replicate_succ]

theorem restoreB_nil (flag : Bool) (a b ta out : Nat) :
    multiplier.step (cfg .restoreB flag a b ta 0 out) = some (cfg .outer false a b ta 0 out) := by
  change some (Cfg.mk (some Label.outer) false (Function.update (stackVals a b ta 0 out) .bTmp [])) =
    some (Cfg.mk (some Label.outer) false (stackVals a b ta 0 out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals,Function.update]

theorem restoreA_cons (flag : Bool) (a b ta bt out : Nat) :
    multiplier.step (cfg .restoreA flag a b (ta+1) bt out) = some (cfg .restoreA true (a+1) b ta bt out) := by
  change some (Cfg.mk (some Label.restoreA) true
    (Function.update (Function.update (stackVals a b (ta+1) bt out) .aTmp (List.replicate ta true))
      .a (true::List.replicate a true))) =
        some (Cfg.mk (some Label.restoreA) true (stackVals (a+1) b ta bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals,Function.update,List.replicate_succ]

theorem restoreA_nil (flag : Bool) (a b bt out : Nat) :
    multiplier.step (cfg .restoreA flag a b 0 bt out) = some (cfg .done false a b 0 bt out) := by
  change some (Cfg.mk (some Label.done) false (Function.update (stackVals a b 0 bt out) .aTmp [])) =
    some (Cfg.mk (some Label.done) false (stackVals a b 0 bt out))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals,Function.update]

/-- Scan one multiplicand, copying one tick to the output per input tick. -/
theorem inner_run (b : Nat) (flag : Bool) (a ta bt out : Nat) :
    ∃ f, runSteps multiplier.step b (cfg .inner flag a b ta bt out) =
      some (cfg .inner f a 0 ta (bt+b) (out+b)) := by
  induction b generalizing flag bt out with
  | zero => exact ⟨flag,by simp [runSteps]⟩
  | succ b ih =>
    obtain ⟨f,h⟩ := ih true (bt+1) (out+1)
    refine ⟨f,?_⟩
    rw [show b+1 = b+1 by rfl,runSteps_front,inner_cons]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Restore a scanned multiplicand without changing its length. -/
theorem restoreB_run (bt : Nat) (flag : Bool) (a b ta out : Nat) :
    ∃ f, runSteps multiplier.step bt (cfg .restoreB flag a b ta bt out) =
      some (cfg .restoreB f a (b+bt) ta 0 out) := by
  induction bt generalizing flag b with
  | zero => exact ⟨flag,by simp [runSteps]⟩
  | succ bt ih =>
    obtain ⟨f,h⟩ := ih true (b+1)
    refine ⟨f,?_⟩
    rw [runSteps_front,restoreB_cons]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Restore the first multiplicand after the outer loop. -/
theorem restoreA_run (ta : Nat) (flag : Bool) (a b bt out : Nat) :
    ∃ f, runSteps multiplier.step ta (cfg .restoreA flag a b ta bt out) =
      some (cfg .restoreA f (a+ta) b 0 bt out) := by
  induction ta generalizing flag a with
  | zero => exact ⟨flag,by simp [runSteps]⟩
  | succ ta ih =>
    obtain ⟨f,h⟩ := ih true (a+1)
    refine ⟨f,?_⟩
    rw [runSteps_front,restoreA_cons]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- One outer iteration copies the entire second operand to the output,
restores it, and consumes one first-operand tick. -/
theorem outer_cycle (flag : Bool) (a b ta out : Nat) :
    runSteps multiplier.step (2*b+3) (cfg .outer flag (a+1) b ta 0 out) =
      some (cfg .outer false a b (ta+1) 0 (out+b)) := by
  obtain ⟨f,hinner⟩ := inner_run b true a (ta+1) 0 out
  simp only [Nat.zero_add] at hinner
  have hi : runSteps multiplier.step (b+1) (cfg .inner true a b (ta+1) 0 out) =
      some (cfg .restoreB false a 0 (ta+1) b (out+b)) := by
    rw [runSteps_add,hinner]
    change multiplier.step (cfg .inner f a 0 (ta+1) b (out+b)) = _
    exact inner_nil f a (ta+1) b (out+b)
  obtain ⟨g,hrestore⟩ := restoreB_run b false a 0 (ta+1) (out+b)
  simp only [Nat.zero_add] at hrestore
  have hr : runSteps multiplier.step (b+1) (cfg .restoreB false a 0 (ta+1) b (out+b)) =
      some (cfg .outer false a b (ta+1) 0 (out+b)) := by
    rw [runSteps_add,hrestore]
    change multiplier.step (cfg .restoreB g a b (ta+1) 0 (out+b)) = _
    exact restoreB_nil g a b (ta+1) (out+b)
  have hn : 2*b+3 = ((b+1)+(b+1))+1 := by omega
  rw [hn,runSteps_front,outer_cons]
  change runSteps multiplier.step ((b+1)+(b+1)) (cfg .inner true a b (ta+1) 0 out) = _
  rw [runSteps_add,hi]
  exact hr

/-- Repeating the outer cycle produces exactly the product number of unary
output ticks while recording all consumed first-operand ticks. -/
theorem outer_run (a : Nat) (flag : Bool) (b ta out : Nat) :
    ∃ f, runSteps multiplier.step (a*(2*b+3)) (cfg .outer flag a b ta 0 out) =
      some (cfg .outer f 0 b (ta+a) 0 (out+a*b)) := by
  induction a generalizing flag ta out with
  | zero => exact ⟨flag,by simp [runSteps]⟩
  | succ a ih =>
    obtain ⟨f,h⟩ := ih false (ta+1) (out+b)
    refine ⟨f,?_⟩
    rw [Nat.succ_mul, Nat.add_comm (a*(2*b+3)) (2*b+3),runSteps_add,outer_cycle]
    simpa [Nat.succ_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- The preloaded unary operands are preserved and their product is added to
the unary output. Exactly `2ab + 4a + 2` blocks are executed. -/
theorem multiply (a b out : Nat) :
    runSteps multiplier.step (2*a*b+4*a+2) (cfg .outer false a b 0 0 out) =
      some (cfg .done false a b 0 0 (out+a*b)) := by
  obtain ⟨f,houter⟩ := outer_run a false b 0 out
  simp only [Nat.zero_add] at houter
  have ho : runSteps multiplier.step (a*(2*b+3)+1) (cfg .outer false a b 0 0 out) =
      some (cfg .restoreA false 0 b a 0 (out+a*b)) := by
    rw [runSteps_add,houter]
    change multiplier.step (cfg .outer f 0 b a 0 (out+a*b)) = _
    exact outer_nil f b a 0 (out+a*b)
  obtain ⟨g,hrestore⟩ := restoreA_run a false 0 b 0 (out+a*b)
  simp only [Nat.zero_add] at hrestore
  have hr : runSteps multiplier.step (a+1) (cfg .restoreA false 0 b a 0 (out+a*b)) =
      some (cfg .done false a b 0 0 (out+a*b)) := by
    rw [runSteps_add,hrestore]
    change multiplier.step (cfg .restoreA g a b 0 0 (out+a*b)) = _
    exact restoreA_nil g a b 0 (out+a*b)
  have hn : 2*a*b+4*a+2 = (a*(2*b+3)+1)+(a+1) := by
    have hab : a*(2*b) = 2*(a*b) := by ac_rfl
    have hba : 2*a*b = 2*(a*b) := by ac_rfl
    rw [hba, Nat.mul_add, hab]
    omega
  rw [hn,runSteps_add,ho]
  exact hr

/-- A quadratic bound in the combined unary operand lengths. -/
theorem time_bound (a b : Nat) : 2*a*b+4*a+2 ≤ 8*(a+b+2)^2 := by
  let n := a+b+2
  have ha : a ≤ n := by dsimp [n]; omega
  have hb : b ≤ n := by dsimp [n]; omega
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hab : a*b ≤ n*n := Nat.mul_le_mul ha hb
  have han : a ≤ n*n := by
    calc
      a = a*1 := by simp
      _ ≤ n*n := Nat.mul_le_mul ha hn
  have hone : 1 ≤ n*n := by
    calc
      1 = 1*1 := by simp
      _ ≤ n*n := Nat.mul_le_mul hn hn
  change 2*a*b+4*a+2 ≤ 8*n^2
  rw [show 2*a*b = 2*(a*b) by ac_rfl, pow_two]
  omega

/-- Kernel-checked trace with two and three input ticks. -/
example : (runSteps multiplier.step 22 (cfg .outer false 2 3 0 0 0)).map
    (fun c => c.stk .output) = some (List.replicate 6 true) := by
  change (Option.map (fun c => c.stk .output) (runSteps multiplier.step 22 (cfg .outer false 2 3 0 0 0)) :
    Option (List Bool)) = some (List.replicate 6 true)
  decide

/-- A zero first operand consumes only the two empty-stack transitions. -/
example : (runSteps multiplier.step 2 (cfg .outer false 0 3 0 0 0)).map
    (fun c => c.stk .output) = some [] := by
  change (Option.map (fun c => c.stk .output) (runSteps multiplier.step 2 (cfg .outer false 0 3 0 0 0)) :
    Option (List Bool)) = some []
  decide

end Shared.ComplexityBridge.TM2UnaryMultiply
