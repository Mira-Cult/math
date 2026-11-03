import Shared.ComplexityBridge.TM2UnaryTransfer

namespace Shared.ComplexityBridge.TM2UnaryProductPhase
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2UnaryMultiply (Stack stackVals)

abbrev ML := Shared.ComplexityBridge.TM2UnaryMultiply.Label
abbrev TL := Shared.ComplexityBridge.TM2UnaryTransfer.Label
abbrev Labels := ML ⊕ TL
abbrev mulMachine := Shared.ComplexityBridge.TM2UnaryMultiply.multiplier
abbrev transferMachine := Shared.ComplexityBridge.TM2UnaryTransfer.machine

/-- Retag every continuation, leaving stack and internal-state operations unchanged. -/
def retag {L L' : Type} (f : L → L') : Stmt (fun _ : Stack => Bool) L Bool →
    Stmt (fun _ : Stack => Bool) L' Bool
  | .push k g s => .push k g (retag f s)
  | .peek k g s => .peek k g (retag f s)
  | .pop k g s => .pop k g (retag f s)
  | .load g s => .load g (retag f s)
  | .branch g s t => .branch g (retag f s) (retag f t)
  | .goto g => .goto (f ∘ g)
  | .halt => .halt

def embed {L L' : Type} (f : L → L')
    (c : Cfg (fun _ : Stack => Bool) L Bool) : Cfg (fun _ : Stack => Bool) L' Bool :=
  ⟨c.l.map f, c.var, c.stk⟩

theorem retag_stepAux {L L' : Type} (f : L → L')
    (s : Stmt (fun _ : Stack => Bool) L Bool) (v : Bool) (stk : Stack → List Bool) :
    stepAux (retag f s) v stk = embed f (stepAux s v stk) := by
  induction s generalizing v stk with
  | halt => rfl
  | goto g => rfl
  | load g s ih => exact ih (g v) stk
  | push k g s ih => exact ih v _
  | peek k g s ih => exact ih (g v (stk k).head?) stk
  | pop k g s ih => exact ih (g v (stk k).head?) _
  | branch g s t ihs iht => by_cases h : g v <;> simp [retag, stepAux, h, ihs, iht]

/-- Both routines share their actual stacks. The two terminal labels dispatch
in one block: multiplication starts transfer, then transfer starts the next
multiplication. -/
def program : Labels → Stmt (fun _ : Stack => Bool) Labels Bool
  | .inl .done => .goto (fun _ => .inr .clear)
  | .inl l => retag Sum.inl (Shared.ComplexityBridge.TM2UnaryMultiply.program l)
  | .inr .ready => .goto (fun _ => .inl .outer)
  | .inr l => retag Sum.inr (Shared.ComplexityBridge.TM2UnaryTransfer.program l)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .a
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Labels
  main := .inl .outer
  σ := Bool
  initialState := false
  m := program

def mulEmbed (c : mulMachine.Cfg) : machine.Cfg := embed Sum.inl c
def transferEmbed (c : transferMachine.Cfg) : machine.Cfg := embed Sum.inr c

def mulTerminal (c : mulMachine.Cfg) : Prop := c.l = some .done
def transferTerminal (c : transferMachine.Cfg) : Prop := c.l = some .ready
noncomputable instance : DecidablePred mulTerminal := fun _ => Classical.propDecidable _
noncomputable instance : DecidablePred transferTerminal := fun _ => Classical.propDecidable _

theorem mul_stable (c : mulMachine.Cfg) (h : mulTerminal c) :
    mulMachine.step c = some c := by
  cases c with
  | mk l v stk =>
    change l = some Shared.ComplexityBridge.TM2UnaryMultiply.Label.done at h
    subst l
    rfl

theorem transfer_stable (c : transferMachine.Cfg) (h : transferTerminal c) :
    transferMachine.step c = some c := by
  cases c with
  | mk l v stk =>
    change l = some Shared.ComplexityBridge.TM2UnaryTransfer.Label.ready at h
    subst l
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem mul_step (c : mulMachine.Cfg) (h : ¬ mulTerminal c) :
    machine.step (mulEmbed c) = (mulMachine.step c).map mulEmbed := by
  cases c with
  | mk l v stk =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | outer | inner | restoreB | restoreA =>
        change some (stepAux (retag Sum.inl (Shared.ComplexityBridge.TM2UnaryMultiply.program _)) v stk) = _
        rw [retag_stepAux]
        rfl

set_option backward.isDefEq.respectTransparency false in
theorem transfer_step (c : transferMachine.Cfg) (h : ¬ transferTerminal c) :
    machine.step (transferEmbed c) = (transferMachine.step c).map transferEmbed := by
  cases c with
  | mk l v stk =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | ready => exact False.elim (h rfl)
      | clear | transfer =>
        change some (stepAux (retag Sum.inr (Shared.ComplexityBridge.TM2UnaryTransfer.program _)) v stk) = _
        rw [retag_stepAux]
        rfl

theorem mul_run (a b out : Nat) :
    ∃ n ≤ 2*a*b+4*a+2,
      runSteps machine.step n
        (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false a b 0 0 out)) =
      some (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .done false a b 0 0 (out+a*b))) := by
  apply Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    mulMachine.step machine.step mulEmbed mulTerminal mul_stable mul_step
  · rfl
  · exact Shared.ComplexityBridge.TM2UnaryMultiply.multiply a b out

theorem transfer_run (a b ta bt out : Nat) :
    ∃ n ≤ a+out+2,
      runSteps machine.step n
        (transferEmbed (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .clear false a b ta bt out)) =
      some (transferEmbed (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .ready false out b ta bt 0)) := by
  apply Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    transferMachine.step machine.step transferEmbed transferTerminal transfer_stable transfer_step
  · rfl
  · exact Shared.ComplexityBridge.TM2UnaryTransfer.reset_and_transfer a b ta bt out

theorem dispatch_mul (a b ta bt out : Nat) :
    machine.step (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .done false a b ta bt out)) =
      some (transferEmbed (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .clear false a b ta bt out)) := by rfl

theorem dispatch_transfer (a b ta bt : Nat) :
    machine.step (transferEmbed (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .ready false a b ta bt 0)) =
      some (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false a b ta bt 0)) := by rfl

/-- A complete multiplication phase, including both handoffs, returns to the
outer label with the product as the first operand and an empty output. -/
theorem product_phase (a b : Nat) :
    ∃ n ≤ (2*a*b+4*a+2) + (a+a*b+2) + 2,
      runSteps machine.step n
        (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false a b 0 0 0)) =
      some (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false (a*b) b 0 0 0)) := by
  obtain ⟨m, hm, hmul⟩ := mul_run a b 0
  simp only [Nat.zero_add] at hmul
  obtain ⟨t, ht, htransfer⟩ := transfer_run a b 0 0 (a*b)
  refine ⟨m+1+t+1, by omega, ?_⟩
  have hn : m+1+t+1 = m+((t+1)+1) := by omega
  rw [hn, runSteps_add, hmul]
  change runSteps machine.step ((t+1)+1)
    (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .done false a b 0 0 (a*b))) = _
  rw [runSteps_front, dispatch_mul]
  change runSteps machine.step (t+1)
    (transferEmbed (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .clear false a b 0 0 (a*b))) = _
  rw [runSteps_add, htransfer]
  change machine.step (transferEmbed (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .ready false (a*b) b 0 0 0)) = _
  exact dispatch_transfer (a*b) b 0 0

/-- Sum of the proved per-phase bounds. The exponent is a fixed parameter
of the eventual finite-control clock wrapper. -/
def powerCost (b : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => powerCost b k + ((2*(b^k)*b+4*(b^k)+2) +
      ((b^k)+(b^k)*b+2) + 2)

/-- Repeatedly executing the same concrete finite program reaches each unary
power. The number of iterations is stated externally; this theorem does not
claim that the machine itself stops after a fixed number of phases. -/
theorem iterated_product (b k : Nat) :
    ∃ n ≤ powerCost b k,
      runSteps machine.step n
        (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 b 0 0 0)) =
      some (mulEmbed (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false (b^k) b 0 0 0)) := by
  induction k with
  | zero => exact ⟨0, by simp [powerCost], by simp [runSteps]⟩
  | succ k ih =>
    obtain ⟨m, hm, hprev⟩ := ih
    obtain ⟨n, hn, hphase⟩ := product_phase (b^k) b
    refine ⟨m+n, by simp only [powerCost]; omega, ?_⟩
    rw [runSteps_add, hprev]
    simpa [pow_succ] using hphase

/-- A polynomial bound in the unary base, for every fixed exponent. -/
theorem powerCost_bound (b k : Nat) : powerCost b k ≤ k*14*(b+2)^k := by
  induction k with
  | zero => simp [powerCost]
  | succ k ih =>
    have hb : 0 < b+2 := by omega
    have hp : (b+2)^k ≤ (b+2)^(k+1) := Nat.pow_le_pow_right hb (by omega)
    have ha : b^k ≤ (b+2)^(k+1) := le_trans (Nat.pow_le_pow_left (by omega) k) hp
    have hab : b^k*b ≤ (b+2)^(k+1) := by
      calc
        b^k*b ≤ (b+2)^k*(b+2) := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) k) (by omega)
        _ = (b+2)^(k+1) := (pow_succ (b+2) k).symm
    have ho : 1 ≤ (b+2)^(k+1) := Nat.one_le_pow _ _ hb
    have hs : 2*(b^k)*b = 2*(b^k*b) := by ac_rfl
    have hm := Nat.mul_le_mul_left (k*14) hp
    simp only [powerCost, hs]
    rw [show (k+1)*14*(b+2)^(k+1) = k*14*(b+2)^(k+1) + 14*(b+2)^(k+1) by simp [Nat.add_mul]]
    omega

namespace FixedPower

abbrev Index (k : Nat) := Fin (k+1)
abbrev Labels (k : Nat) := Index k × TM2UnaryProductPhase.Labels

def advance {k : Nat} (i : Index k) (h : i.val < k) : Index k := ⟨i.val+1, by omega⟩

def program (k : Nat) : Labels k → Stmt (fun _ : Stack => Bool) (Labels k) Bool
  | (i, l) => if h : i.val < k then
      match l with
      | .inl .done => .goto (fun _ => (i, .inr .clear))
      | .inl l => retag (fun q => (i, Sum.inl q)) (Shared.ComplexityBridge.TM2UnaryMultiply.program l)
      | .inr .ready => .goto (fun _ => (advance i h, .inl .outer))
      | .inr l => retag (fun q => (i, Sum.inr q)) (Shared.ComplexityBridge.TM2UnaryTransfer.program l)
    else .goto (fun _ => (i,l))

def machine (k : Nat) : Turing.FinTM2 where
  K := Stack
  k₀ := .a
  k₁ := .a
  Γ := fun _ => Bool
  Λ := Labels k
  main := (⟨0, by omega⟩, .inl .outer)
  σ := Bool
  initialState := false
  m := program k

def mulEmbed {k : Nat} (i : Index k) (c : mulMachine.Cfg) : (machine k).Cfg :=
  embed (fun q => (i, Sum.inl q)) c

def transferEmbed {k : Nat} (i : Index k) (c : transferMachine.Cfg) : (machine k).Cfg :=
  embed (fun q => (i, Sum.inr q)) c

set_option backward.isDefEq.respectTransparency false in
theorem mul_step {k : Nat} (i : Index k) (hi : i.val < k) (c : mulMachine.Cfg) (h : ¬ mulTerminal c) :
    (machine k).step (mulEmbed i c) = (mulMachine.step c).map (mulEmbed i) := by
  cases c with
  | mk l v stk =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | outer | inner | restoreB | restoreA =>
        change some (stepAux (program k (i, .inl _)) v stk) = _
        simp only [program, dif_pos hi]
        rw [retag_stepAux]
        rfl

set_option backward.isDefEq.respectTransparency false in
theorem transfer_step {k : Nat} (i : Index k) (hi : i.val < k) (c : transferMachine.Cfg)
    (h : ¬ transferTerminal c) :
    (machine k).step (transferEmbed i c) = (transferMachine.step c).map (transferEmbed i) := by
  cases c with
  | mk l v stk =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | ready => exact False.elim (h rfl)
      | clear | transfer =>
        change some (stepAux (program k (i, .inr _)) v stk) = _
        simp only [program, dif_pos hi]
        rw [retag_stepAux]
        rfl

theorem mul_run {k : Nat} (i : Index k) (hi : i.val < k) (a b out : Nat) :
    ∃ n ≤ 2*a*b+4*a+2,
      runSteps (machine k).step n
        (mulEmbed i (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false a b 0 0 out)) =
      some (mulEmbed i (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .done false a b 0 0 (out+a*b))) := by
  apply Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    mulMachine.step (machine k).step (mulEmbed i) mulTerminal mul_stable (mul_step i hi)
  · rfl
  · exact Shared.ComplexityBridge.TM2UnaryMultiply.multiply a b out

theorem transfer_run {k : Nat} (i : Index k) (hi : i.val < k) (a b ta bt out : Nat) :
    ∃ n ≤ a+out+2,
      runSteps (machine k).step n
        (transferEmbed i (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .clear false a b ta bt out)) =
      some (transferEmbed i (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .ready false out b ta bt 0)) := by
  apply Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    transferMachine.step (machine k).step (transferEmbed i) transferTerminal transfer_stable (transfer_step i hi)
  · rfl
  · exact Shared.ComplexityBridge.TM2UnaryTransfer.reset_and_transfer a b ta bt out

theorem dispatch_mul {k : Nat} (i : Index k) (hi : i.val < k) (a b ta bt out : Nat) :
    (machine k).step (mulEmbed i (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .done false a b ta bt out)) =
      some (transferEmbed i (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .clear false a b ta bt out)) := by
  change some (stepAux (program k (i, .inl .done)) false (stackVals a b ta bt out)) = _
  simp only [program, dif_pos hi, stepAux]
  rfl

theorem dispatch_transfer {k : Nat} (i : Index k) (hi : i.val < k) (a b ta bt : Nat) :
    (machine k).step (transferEmbed i (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .ready false a b ta bt 0)) =
      some (mulEmbed (advance i hi) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false a b ta bt 0)) := by
  change some (stepAux (program k (i, .inr .ready)) false (stackVals a b ta bt 0)) = _
  simp only [program, dif_pos hi, stepAux]
  rfl

theorem product_phase {k : Nat} (i : Index k) (hi : i.val < k) (a b : Nat) :
    ∃ n ≤ (2*a*b+4*a+2) + (a+a*b+2) + 2,
      runSteps (machine k).step n
        (mulEmbed i (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false a b 0 0 0)) =
      some (mulEmbed (advance i hi) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false (a*b) b 0 0 0)) := by
  obtain ⟨m, hm, hmul⟩ := mul_run i hi a b 0
  simp only [Nat.zero_add] at hmul
  obtain ⟨t, ht, htransfer⟩ := transfer_run i hi a b 0 0 (a*b)
  refine ⟨m+1+t+1, by omega, ?_⟩
  have hn : m+1+t+1 = m+((t+1)+1) := by omega
  rw [hn, runSteps_add, hmul]
  change runSteps (machine k).step ((t+1)+1)
    (mulEmbed i (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .done false a b 0 0 (a*b))) = _
  rw [runSteps_front, dispatch_mul i hi]
  change runSteps (machine k).step (t+1)
    (transferEmbed i (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .clear false a b 0 0 (a*b))) = _
  rw [runSteps_add, htransfer]
  change (machine k).step (transferEmbed i (Shared.ComplexityBridge.TM2UnaryTransfer.cfg .ready false (a*b) b 0 0 0)) = _
  exact dispatch_transfer i hi (a*b) b 0 0

def index (k j : Nat) (h : j ≤ k) : Index k := ⟨j, by omega⟩

/-- The finite control advances exactly once per completed multiplication.
The input stacks are explicit: one first-operand tick, `b` base ticks, and
empty temporary and output stacks. -/
theorem iterate (k j b : Nat) (hj : j ≤ k) :
    ∃ n ≤ powerCost b j,
      runSteps (machine k).step n
        (mulEmbed (index k 0 (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 b 0 0 0)) =
      some (mulEmbed (index k j hj) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false (b^j) b 0 0 0)) := by
  induction j with
  | zero => exact ⟨0, by simp [powerCost], by simp [runSteps, index]⟩
  | succ j ih =>
    have hj' : j ≤ k := by omega
    obtain ⟨m, hm, hprev⟩ := ih hj'
    let i : Index k := index k j hj'
    have hi : i.val < k := by dsimp [i, index]; omega
    obtain ⟨n, hn, hphase⟩ := product_phase i hi (b^j) b
    have hnext : advance i hi = index k (j+1) hj := by
      apply Fin.ext
      rfl
    refine ⟨m+n, by simp only [powerCost]; omega, ?_⟩
    rw [runSteps_add, hprev]
    simpa [i, hnext, pow_succ] using hphase

/-- With the exponent fixed in the finite label type, the machine reaches
its completed phase in at most a polynomial number of TM2 blocks. -/
theorem fixed_power (k b : Nat) :
    ∃ n ≤ k*14*(b+2)^k,
      runSteps (machine k).step n
        (mulEmbed (index k 0 (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 b 0 0 0)) =
      some (mulEmbed (index k k (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false (b^k) b 0 0 0)) := by
  obtain ⟨n, hn, hrun⟩ := iterate k k b (by omega)
  exact ⟨n, le_trans hn (powerCost_bound b k), hrun⟩

/-- The completed phase is a self-loop, not an ordinary halt. -/
theorem completed_step (k a b : Nat) :
    (machine k).step
      (mulEmbed (index k k (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false a b 0 0 0)) =
    some (mulEmbed (index k k (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false a b 0 0 0)) := by
  change some (stepAux (program k (index k k (by omega), .inl .outer)) false (stackVals a b 0 0 0)) = _
  simp only [program, index, Nat.lt_irrefl, ↓reduceDIte, stepAux]
  rfl

/-- Two phases, including both handoffs in each phase, produce four ticks. -/
example : (runSteps (machine 2).step 45
    (mulEmbed (index 2 0 (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 2 0 0 0))).map
      (fun c => c.stk .a) = some (List.replicate 4 true) := by
  change (Option.map (fun c => c.stk .a) (runSteps (machine 2).step 45
    (mulEmbed (index 2 0 (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 2 0 0 0))) :
      Option (List Bool)) = some (List.replicate 4 true)
  decide

/-- Exponent zero starts at the completed phase with the one tick for `b^0`. -/
example (b : Nat) : (machine 0).step
    (mulEmbed (index 0 0 (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 b 0 0 0)) =
      some (mulEmbed (index 0 0 (by omega)) (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 b 0 0 0)) :=
  completed_step 0 1 b

end FixedPower
end Shared.ComplexityBridge.TM2UnaryProductPhase
