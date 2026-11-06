import Shared.ComplexityBridge.TM2PairLength

namespace Shared.ComplexityBridge.TM2PairPower
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev LStack := Shared.ComplexityBridge.TM2PairLength.Stack
abbrev LLabel := Shared.ComplexityBridge.TM2PairLength.Label
abbrev PStack := Shared.ComplexityBridge.TM2UnaryMultiply.Stack
abbrev PLabel (k : Nat) := Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.Labels k
abbrev Loader := Shared.ComplexityBridge.TM2PairLength.machine
abbrev Power := Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.machine
abbrev K := Bool ⊕ PStack
abbrev Labels (k : Nat) := LLabel ⊕ PLabel k

def loadKey : LStack → K
  | .input => .inl false
  | .scratch => .inl true
  | .ticks => .inr .b

def loadStacks (S : LStack → List Bool) (other : PStack → List Bool) : K → List Bool
  | .inl false => S .input
  | .inl true => S .scratch
  | .inr .b => S .ticks
  | .inr k => other k

def powerStacks (input scratch : List Bool) (S : PStack → List Bool) : K → List Bool
  | .inl false => input
  | .inl true => scratch
  | .inr k => S k

@[simp] theorem loadStacks_loadKey (S : LStack → List Bool) (other : PStack → List Bool) (s : LStack) :
    loadStacks S other (loadKey s) = S s := by cases s <;> rfl

theorem loadStacks_update (S : LStack → List Bool) (other : PStack → List Bool)
    (k : LStack) (xs : List Bool) :
    loadStacks (Function.update S k xs) other = Function.update (loadStacks S other) (loadKey k) xs := by
  funext j
  cases k <;> cases j with
  | inl b => cases b <;> simp [loadStacks,loadKey,Function.update]
  | inr j => cases j <;> simp [loadStacks,loadKey,Function.update]

theorem powerStacks_update (input scratch : List Bool) (S : PStack → List Bool)
    (k : PStack) (xs : List Bool) :
    powerStacks input scratch (Function.update S k xs) =
      Function.update (powerStacks input scratch S) (.inr k) xs := by
  funext j
  cases j with
  | inl b => cases b <;> simp [powerStacks,Function.update]
  | inr j =>
    by_cases h : j = k
    · subst j; simp [powerStacks,Function.update]
    · have hh : Sum.inr j ≠ (Sum.inr k : K) := by simpa using h
      simp [powerStacks,Function.update_of_ne h,Function.update_of_ne hh]

def liftLoad {k : Nat} : Stmt (fun _ : LStack => Bool) LLabel (Option Bool) →
    Stmt (fun _ : K => Bool) (Labels k) (Option Bool × Bool)
  | .push s f q => .push (loadKey s) (fun v => f v.1) (liftLoad q)
  | .peek s f q => .peek (loadKey s) (fun v h => (f v.1 h,v.2)) (liftLoad q)
  | .pop s f q => .pop (loadKey s) (fun v h => (f v.1 h,v.2)) (liftLoad q)
  | .load f q => .load (fun v => (f v.1,v.2)) (liftLoad q)
  | .branch f q r => .branch (fun v => f v.1) (liftLoad q) (liftLoad r)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .halt

def liftPower {k : Nat} : Stmt (fun _ : PStack => Bool) (PLabel k) Bool →
    Stmt (fun _ : K => Bool) (Labels k) (Option Bool × Bool)
  | .push s f q => .push (.inr s) (fun v => f v.2) (liftPower q)
  | .peek s f q => .peek (.inr s) (fun v h => (v.1,f v.2 h)) (liftPower q)
  | .pop s f q => .pop (.inr s) (fun v h => (v.1,f v.2 h)) (liftPower q)
  | .load f q => .load (fun v => (v.1,f v.2)) (liftPower q)
  | .branch f q r => .branch (fun v => f v.2) (liftPower q) (liftPower r)
  | .goto f => .goto (fun v => .inr (f v.2))
  | .halt => .halt

def loadCfg {k : Nat} (other : PStack → List Bool) (flag : Bool) (c : Loader.Cfg) :
    Cfg (fun _ : K => Bool) (Labels k) (Option Bool × Bool) :=
  ⟨c.l.map Sum.inl,(c.var,flag),loadStacks c.stk other⟩

def powerCfg {k : Nat} (input scratch : List Bool) (flag : Option Bool) (c : (Power k).Cfg) :
    Cfg (fun _ : K => Bool) (Labels k) (Option Bool × Bool) :=
  ⟨c.l.map Sum.inr,(flag,c.var),powerStacks input scratch c.stk⟩

set_option backward.isDefEq.respectTransparency false in
theorem liftLoad_aux {k : Nat} (q : Stmt (fun _ : LStack => Bool) LLabel (Option Bool))
    (v : Option Bool) (flag : Bool) (S : LStack → List Bool) (other : PStack → List Bool) :
    stepAux (liftLoad (k := k) q) (v,flag) (loadStacks S other) =
      loadCfg other flag (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push s f q ih =>
    simp only [liftLoad,stepAux,loadStacks_loadKey]
    rw [← loadStacks_update S other s (f v::S s)]
    exact ih v _
  | peek s f q ih =>
    simp only [liftLoad,stepAux,loadStacks_loadKey]
    exact ih (f v (S s).head?) S
  | pop s f q ih =>
    simp only [liftLoad,stepAux,loadStacks_loadKey]
    rw [← loadStacks_update S other s (S s).tail]
    exact ih (f v (S s).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftLoad,stepAux,h,ihq,ihr]

theorem liftPower_aux {k : Nat} (q : Stmt (fun _ : PStack => Bool) (PLabel k) Bool)
    (v : Bool) (flag : Option Bool) (S : PStack → List Bool) (input scratch : List Bool) :
    stepAux (liftPower q) (flag,v) (powerStacks input scratch S) =
      powerCfg input scratch flag (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push s f q ih =>
    simp only [liftPower,stepAux,powerStacks]
    rw [← powerStacks_update input scratch S s (f v::S s)]
    exact ih v _
  | peek s f q ih =>
    change stepAux (liftPower q) (flag,f v (S s).head?) (powerStacks input scratch S) = _
    exact ih (f v (S s).head?) S
  | pop s f q ih =>
    simp only [liftPower,stepAux,powerStacks]
    rw [← powerStacks_update input scratch S s (S s).tail]
    exact ih (f v (S s).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftPower,stepAux,h,ihq,ihr]

/-- One table executes the canonical-input loader, then initializes the first
power operand and dispatches to the fixed-exponent arithmetic program. -/
def program (k : Nat) : Labels k → Stmt (fun _ : K => Bool) (Labels k) (Option Bool × Bool)
  | .inl .done => .push (.inr .a) (fun _ => true)
      (.goto (fun _ => .inr ((⟨0,by omega⟩), .inl .outer)))
  | .inl l => liftLoad (Shared.ComplexityBridge.TM2PairLength.program l)
  | .inr l => liftPower (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.program k l)

def machine (k : Nat) : Turing.FinTM2 where
  K := K
  k₀ := .inl false
  k₁ := .inr .a
  Γ := fun _ => Bool
  Λ := Labels k
  main := .inl .start
  σ := Option Bool × Bool
  initialState := (none,false)
  m := program k

def loadTerminal (c : Loader.Cfg) : Prop := c.l = some .done
noncomputable instance : DecidablePred loadTerminal := fun _ => Classical.propDecidable _

theorem load_stable (c : Loader.Cfg) (h : loadTerminal c) : Loader.step c = some c := by
  cases c with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2PairLength.Label.done at h
    subst l
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem load_step {k : Nat} (other : PStack → List Bool) (flag : Bool) (c : Loader.Cfg)
    (h : ¬ loadTerminal c) :
    (machine k).step (loadCfg other flag c) = (Loader.step c).map (loadCfg other flag) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | start | x0 | x1 | x2 | x3 | x4 | x5 | w0 | w1 | w2 | restore =>
        change some (stepAux (liftLoad (Shared.ComplexityBridge.TM2PairLength.program _)) (v,flag)
          (loadStacks S other)) = _
        rw [liftLoad_aux]
        rfl

set_option backward.isDefEq.respectTransparency false in
theorem power_step {k : Nat} (input scratch : List Bool) (flag : Option Bool) (c : (Power k).Cfg) :
    (machine k).step (powerCfg input scratch flag c) = ((Power k).step c).map (powerCfg input scratch flag) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftPower (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.program k l))
        (flag,v) (powerStacks input scratch S)) = _
      rw [liftPower_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem power_run {k : Nat} (input scratch : List Bool) (flag : Option Bool) (c : (Power k).Cfg) (n : Nat) :
    runSteps (machine k).step n (powerCfg input scratch flag c) =
      (runSteps (Power k).step n c).map (powerCfg input scratch flag) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front, runSteps_front, power_step]
    cases h : (Power k).step c with
    | none => rfl
    | some c' => exact ih c'

theorem initial_eq (k : Nat) (bits : List Bool) :
    Turing.initList (machine k) bits = loadCfg (k := k) (fun _ => []) false (Turing.initList Loader bits) := by
  rw [Shared.ComplexityBridge.TM2PairLength.initial_eq]
  change (Cfg.mk (some (Sum.inl Shared.ComplexityBridge.TM2PairLength.Label.start)) (none,false) _ : (machine k).Cfg) =
    Cfg.mk (some (Sum.inl Shared.ComplexityBridge.TM2PairLength.Label.start)) (none,false)
      (loadStacks (Shared.ComplexityBridge.TM2PairLength.stackVals bits [] 0) (fun _ => []))
  congr 1
  funext j
  cases j with
  | inl b => cases b <;> simp [machine,loadStacks,Shared.ComplexityBridge.TM2PairLength.stackVals] <;> rfl
  | inr s => cases s <;> simp [machine,loadStacks,Shared.ComplexityBridge.TM2PairLength.stackVals]

def powerStart (k b : Nat) : (Power k).Cfg :=
  Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.mulEmbed
    (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index k 0 (by omega))
    (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false 1 b 0 0 0)

def powerFinished (k b : Nat) : (Power k).Cfg :=
  Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.mulEmbed
    (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index k k (by omega))
    (Shared.ComplexityBridge.TM2UnaryMultiply.cfg .outer false (b^k) b 0 0 0)

theorem loader_run (k : Nat) (x w : List Bool) :
    ∃ n ≤ 2*(BitstringEncoding.bitEncode (x,w)).length+3,
      runSteps (machine k).step n (Turing.initList (machine k) (BitstringEncoding.bitEncode (x,w))) =
        some (loadCfg (k := k) (fun _ => []) false
          (Shared.ComplexityBridge.TM2PairLength.cfg .done none (BitstringEncoding.bitEncode (x,w)) []
            (x.length+w.length+2))) := by
  rw [initial_eq]
  apply Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Loader.step (machine k).step (loadCfg (fun _ => []) false) loadTerminal load_stable (load_step (fun _ => []) false)
  · rfl
  · exact Shared.ComplexityBridge.TM2PairLength.load_pair_correct x w

theorem dispatch (k : Nat) (bits : List Bool) (b : Nat) :
    (machine k).step (loadCfg (k := k) (fun _ => []) false
      (Shared.ComplexityBridge.TM2PairLength.cfg .done none bits [] b)) =
    some (powerCfg bits [] none (powerStart k b)) := by
  change some (Cfg.mk (some (Sum.inr ((⟨0,by omega⟩), Sum.inl Shared.ComplexityBridge.TM2UnaryMultiply.Label.outer))) (none,false)
    (Function.update (loadStacks (Shared.ComplexityBridge.TM2PairLength.stackVals bits [] b) (fun _ => []))
      (.inr .a) [true]) : (machine k).Cfg) = _
  congr 1
  congr 1
  change Function.update (loadStacks (Shared.ComplexityBridge.TM2PairLength.stackVals bits [] b) (fun _ => []))
    (.inr .a) [true] = powerStacks bits [] (Shared.ComplexityBridge.TM2UnaryMultiply.stackVals 1 b 0 0 0)
  funext j
  cases j with
  | inl v => cases v <;> simp [powerStacks, loadStacks, Shared.ComplexityBridge.TM2PairLength.stackVals, Function.update]
  | inr s => cases s <;> simp [powerStacks, loadStacks, Shared.ComplexityBridge.TM2PairLength.stackVals,
      Shared.ComplexityBridge.TM2UnaryMultiply.stackVals, Function.update]

set_option backward.isDefEq.respectTransparency false in
/-- From the canonical pair input, generate the exact raw-length power while
preserving the complete input encoding. All loading, dispatch, and arithmetic
blocks are included in the bound. -/
theorem pair_power (k : Nat) (x w : List Bool) :
    ∃ n ≤ (2*(BitstringEncoding.bitEncode (x,w)).length+3) + 1 +
        k*14*(x.length+w.length+4)^k,
      runSteps (machine k).step n (Turing.initList (machine k) (BitstringEncoding.bitEncode (x,w))) =
        some (powerCfg (BitstringEncoding.bitEncode (x,w)) [] none
          (powerFinished k (x.length+w.length+2))) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let b := x.length+w.length+2
  obtain ⟨m, hm, hload⟩ := loader_run k x w
  obtain ⟨t, ht, hpower⟩ := Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.fixed_power k b
  have hp : runSteps (machine k).step t (powerCfg bits [] none (powerStart k b)) =
      some (powerCfg bits [] none (powerFinished k b)) := by
    rw [power_run]
    change (runSteps (Power k).step t _).map (powerCfg bits [] none) = _
    have hpower' : runSteps (Power k).step t (powerStart k b) = some (powerFinished k b) := by
      simpa [powerStart,powerFinished] using hpower
    rw [hpower']
    rfl
  refine ⟨m+1+t, ?_, ?_⟩
  · dsimp [b] at ht
    have hb : x.length+w.length+2+2 = x.length+w.length+4 := by omega
    rw [hb] at ht
    omega
  · have hn : m+1+t = m+(t+1) := by omega
    rw [hn, runSteps_add, hload]
    change runSteps (machine k).step (t+1) (loadCfg (k := k) (fun _ => []) false
      (Shared.ComplexityBridge.TM2PairLength.cfg .done none bits [] b)) = _
    rw [runSteps_front, dispatch]
    exact hp

/-- Expose the observable stacks of the composed machine. -/
theorem pair_power_stacks (k : Nat) (x w : List Bool) :
    ∃ n ≤ (2*(BitstringEncoding.bitEncode (x,w)).length+3) + 1 +
        k*14*(x.length+w.length+4)^k,
      ∃ c, runSteps (machine k).step n (Turing.initList (machine k) (BitstringEncoding.bitEncode (x,w))) = some c ∧
        c.stk (.inl false) = BitstringEncoding.bitEncode (x,w) ∧
        c.stk (.inr .a) = List.replicate ((x.length+w.length+2)^k) true ∧
        c.stk (.inr .b) = List.replicate (x.length+w.length+2) true := by
  obtain ⟨n, hn, h⟩ := pair_power k x w
  refine ⟨n, hn, _, h, ?_, ?_, ?_⟩ <;>
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Completion is a self-loop of the composed machine. -/
theorem finished_step (k : Nat) (bits : List Bool) (b : Nat) :
    (machine k).step (powerCfg bits [] none (powerFinished k b)) =
      some (powerCfg bits [] none (powerFinished k b)) := by
  rw [power_step]
  have h : (Power k).step (powerFinished k b) = some (powerFinished k b) := by
    exact Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.completed_step k (b^k) b
  rw [h]
  rfl

example : (runSteps (machine 1).step 23
    (Turing.initList (machine 1) (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))).map
      (fun c => c.stk (.inr .a)) = some (List.replicate 2 true) := by
  change (Option.map (fun c => c.stk (.inr .a)) (runSteps (machine 1).step 23
    (Turing.initList (machine 1) (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))) :
      Option (List Bool)) = _
  decide

end Shared.ComplexityBridge.TM2PairPower
