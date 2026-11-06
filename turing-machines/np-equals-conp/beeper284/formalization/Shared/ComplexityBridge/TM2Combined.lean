import Shared.ComplexityBridge.TM2Loader

namespace Shared.ComplexityBridge.TM2Combined
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.ComplexityBridge.TM2FiniteReverse
open Shared.ComplexityBridge.TM2Loader Shared.Codes.TM2Program Shared.Codes.TM2Statements
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2FiniteBoundary
open Shared.ComplexityBridge.TM2BooleanOutput

abbrev Alphabet (ks symbols : Nat) : (Bool ⊕ Fin (ks+1)) → Type
  | .inl _ => Bool
  | .inr _ => Fin (symbols+1)

abbrev CoreStmt (ks states symbols labels : Nat) :=
  Stmt (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1))

def liftStmt (ks states symbols labels : Nat) : CoreStmt ks states symbols labels →
    Stmt (Alphabet ks symbols) (Bool ⊕ Fin (labels+1)) (Option Bool × Fin (states+1))
  | .push k f q => .push (.inr k) (fun v => f v.2) (liftStmt ks states symbols labels q)
  | .peek k f q => .peek (.inr k) (fun v h => (v.1,f v.2 h)) (liftStmt ks states symbols labels q)
  | .pop k f q => .pop (.inr k) (fun v h => (v.1,f v.2 h)) (liftStmt ks states symbols labels q)
  | .load f q => .load (fun v => (v.1,f v.2)) (liftStmt ks states symbols labels q)
  | .branch f a b => .branch (fun v => f v.2) (liftStmt ks states symbols labels a) (liftStmt ks states symbols labels b)
  | .goto f => .goto (fun v => .inr (f v.2))
  | .halt => .halt

def embedStacks (ks symbols : Nat) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)
  | .inl false => a
  | .inl true => b
  | .inr k => S k

def embedCfg (ks states symbols labels : Nat) (flag : Option Bool) (a b : List Bool)
    (c : Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1))) :
    Cfg (Alphabet ks symbols) (Bool ⊕ Fin (labels+1)) (Option Bool × Fin (states+1)) :=
  ⟨c.l.map Sum.inr, (flag,c.var), embedStacks ks symbols a b c.stk⟩

theorem embedStacks_update (ks symbols : Nat) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (k : Fin (ks+1)) (xs : List (Fin (symbols+1))) :
    embedStacks ks symbols a b (Function.update S k xs) =
      Function.update (embedStacks ks symbols a b S) (.inr k) xs := by
  funext j
  cases j with
  | inl v => cases v <;> simp [embedStacks, Function.update]
  | inr j =>
    by_cases h : j = k
    · subst j; simp [embedStacks, Function.update]
    · have hh : Sum.inr j ≠ (Sum.inr k : Bool ⊕ Fin (ks+1)) := by simpa using h
      simp [embedStacks, Function.update_of_ne h, Function.update_of_ne hh]

/-- Lifting a core statement preserves its whole-block step and keeps the
Boolean loader stacks unchanged. -/
theorem lift_stepAux (ks states symbols labels : Nat) (q : CoreStmt ks states symbols labels)
    (v : Fin (states+1)) (flag : Option Bool) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    stepAux (liftStmt ks states symbols labels q) (flag,v) (embedStacks ks symbols a b S) =
      embedCfg ks states symbols labels flag a b (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push k f q ih =>
    simp only [liftStmt, stepAux, embedStacks]
    rw [← embedStacks_update ks symbols a b S k (f v :: S k)]
    exact ih v _
  | peek k f q ih =>
    change stepAux (liftStmt ks states symbols labels q) (flag,f v (S k).head?) (embedStacks ks symbols a b S) = _
    exact ih (f v (S k).head?) S
  | pop k f q ih =>
    simp only [liftStmt, stepAux, embedStacks]
    rw [← embedStacks_update ks symbols a b S k (S k).tail]
    exact ih (f v (S k).head?) _
  | branch f l r ihl ihr =>
    by_cases h : f v <;> simp [liftStmt, stepAux, h, ihl, ihr]

/-- The two loader labels are followed directly by the lifted core program. -/
def program (ks states symbols : Nat) (p : Program) (input main z o : Nat) :
    Bool ⊕ Fin (p.length+1) → Stmt (Alphabet ks symbols) (Bool ⊕ Fin (p.length+1))
      (Option Bool × Fin (states+1))
  | .inl false => .pop (.inl false) (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.push (.inl true) (fun v => v.1.getD false) (.goto (fun _ => .inl false)))
        (.goto (fun _ => .inl true)))
  | .inl true => .pop (.inl true) (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.push (.inr (clip ks input)) (fun v => enc symbols z o (v.1.getD false))
          (.goto (fun _ => .inl true)))
        (.goto (fun _ => .inr (clip p.length main))))
  | .inr l => liftStmt ks states symbols p.length (finiteProgram ks states symbols p l)

def machine (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inr (clip ks output)
  Γ := Alphabet ks symbols
  Λ := Bool ⊕ Fin (p.length+1)
  main := .inl false
  σ := Option Bool × Fin (states+1)
  initialState := (none,clip states initial)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols p input main z o

set_option backward.isDefEq.respectTransparency false in
/-- The core's entire configuration is embedded in the combined machine. -/
theorem core_step (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (c : (finiteCore ks states symbols p input output main initial).Cfg)
    (flag : Option Bool) (a b : List Bool) :
    (machine ks states symbols p input output main initial z o).step (embedCfg ks states symbols p.length flag a b c) =
      ((finiteCore ks states symbols p input output main initial).step c).map (embedCfg ks states symbols p.length flag a b) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftStmt ks states symbols p.length (finiteProgram ks states symbols p l))
        (flag,v) (embedStacks ks symbols a b S)) = _
      rw [lift_stepAux]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- A finite core run is reproduced block for block by the combined machine. -/
theorem core_run (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (c : (finiteCore ks states symbols p input output main initial).Cfg)
    (flag : Option Bool) (a b : List Bool) (n : Nat) :
    runSteps (machine ks states symbols p input output main initial z o).step n
      (embedCfg ks states symbols p.length flag a b c) =
      (runSteps (finiteCore ks states symbols p input output main initial).step n c).map
        (embedCfg ks states symbols p.length flag a b) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front, runSteps_front, core_step]
    cases h : (finiteCore ks states symbols p input output main initial).step c with
    | none => rfl
    | some c' => exact ih c'

def loadStacks (ks symbols input : Nat) (a b : List Bool) (os : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k) :=
  embedStacks ks symbols a b (Function.update S (clip ks input) os)

def loadCfg (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (label : Bool) (flag : Option Bool) (a b : List Bool) (os : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) : (machine ks states symbols p input output main initial z o).Cfg :=
  ⟨some (.inl label), (flag,clip states initial), loadStacks ks symbols input a b os S⟩

theorem combined_scan_cons (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (flag : Option Bool) (x : Bool) (xs ys : List Bool) (os : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols p input output main initial z o).step
      (loadCfg ks states symbols p input output main initial z o false flag (x::xs) ys os S) =
      some (loadCfg ks states symbols p input output main initial z o false (some x) xs (x::ys) os S) := by
  change some (Cfg.mk (some (Sum.inl false : Bool ⊕ Fin (p.length+1))) (some x,clip states initial)
    (Function.update (Function.update (loadStacks ks symbols input (x::xs) ys os S) (.inl false) xs)
      (.inl true) (x::ys))) = some (Cfg.mk (some (Sum.inl false : Bool ⊕ Fin (p.length+1))) (some x,clip states initial)
        (loadStacks ks symbols input xs (x::ys) os S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [loadStacks, embedStacks, Function.update]
  | inr j => simp [loadStacks, embedStacks, Function.update]

theorem combined_scan_nil (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (flag : Option Bool) (ys : List Bool) (os : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols p input output main initial z o).step
      (loadCfg ks states symbols p input output main initial z o false flag [] ys os S) =
      some (loadCfg ks states symbols p input output main initial z o true none [] ys os S) := by
  change some (Cfg.mk (some (Sum.inl true : Bool ⊕ Fin (p.length+1))) (none,clip states initial)
    (Function.update (loadStacks ks symbols input [] ys os S) (.inl false) [])) =
      some (Cfg.mk (some (Sum.inl true : Bool ⊕ Fin (p.length+1))) (none,clip states initial) (loadStacks ks symbols input [] ys os S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [loadStacks, embedStacks, Function.update]
  | inr j => simp [loadStacks, embedStacks, Function.update]

theorem combined_restore_cons (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (flag : Option Bool) (x : Bool) (xs : List Bool) (os : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols p input output main initial z o).step
      (loadCfg ks states symbols p input output main initial z o true flag [] (x::xs) os S) =
      some (loadCfg ks states symbols p input output main initial z o true (some x) [] xs (enc symbols z o x::os) S) := by
  simp only [Turing.FinTM2.step, Turing.TM2.step, machine, loadCfg, program, stepAux, loadStacks, embedStacks]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some]
  congr 1
  simp only [Bool.cond_true]
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [embedStacks, Function.update]
  | inr j =>
    by_cases h : j = clip ks input
    · subst j; simp [embedStacks, Function.update]
    · simp [embedStacks, Function.update, h]

def coreInit (ks states symbols : Nat) (p : Program) (input output main initial : Nat)
    (os : List (Fin (symbols+1))) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (finiteCore ks states symbols p input output main initial).Cfg :=
  ⟨some (clip p.length main),clip states initial,Function.update S (clip ks input) os⟩

theorem combined_restore_nil (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (flag : Option Bool) (os : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols p input output main initial z o).step
      (loadCfg ks states symbols p input output main initial z o true flag [] [] os S) =
      some (embedCfg ks states symbols p.length none [] [] (coreInit ks states symbols p input output main initial os S)) := by
  change some (Cfg.mk (some (Sum.inr (clip p.length main) : Bool ⊕ Fin (p.length+1))) (none,clip states initial)
    (Function.update (loadStacks ks symbols input [] [] os S) (.inl true) [])) =
      some (Cfg.mk (some (Sum.inr (clip p.length main) : Bool ⊕ Fin (p.length+1))) (none,clip states initial)
        (loadStacks ks symbols input [] [] os S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [loadStacks, embedStacks, Function.update]
  | inr j => simp [loadStacks, embedStacks, Function.update]

/-- The shared machine's first pass. -/
theorem combined_scan_run (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (xs ys : List Bool) (os : List (Fin (symbols+1))) (S : Fin (ks+1) → List (Fin (symbols+1)))
    (flag : Option Bool) :
    ∃ v, runSteps (machine ks states symbols p input output main initial z o).step xs.length
      (loadCfg ks states symbols p input output main initial z o false flag xs ys os S) =
      some (loadCfg ks states symbols p input output main initial z o false v [] (xs.reverse++ys) os S) := by
  induction xs generalizing ys flag with
  | nil => exact ⟨flag, by simp [runSteps]⟩
  | cons x xs ih =>
    obtain ⟨v,hv⟩ := ih (x::ys) (some x)
    refine ⟨v, ?_⟩
    rw [List.length_cons, runSteps_front, combined_scan_cons]
    simpa [List.reverse_cons, List.append_assoc] using hv

/-- The shared machine's second pass. -/
theorem combined_restore_run (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (xs : List Bool) (os : List (Fin (symbols+1))) (S : Fin (ks+1) → List (Fin (symbols+1)))
    (flag : Option Bool) :
    ∃ v, runSteps (machine ks states symbols p input output main initial z o).step xs.length
      (loadCfg ks states symbols p input output main initial z o true flag [] xs os S) =
      some (loadCfg ks states symbols p input output main initial z o true v [] [] (xs.reverse.map (enc symbols z o) ++ os) S) := by
  induction xs generalizing os flag with
  | nil => exact ⟨flag, by simp [runSteps]⟩
  | cons x xs ih =>
    obtain ⟨v,hv⟩ := ih (enc symbols z o x::os) (some x)
    refine ⟨v, ?_⟩
    rw [List.length_cons, runSteps_front, combined_restore_cons]
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using hv

/-- The combined loader starts from the library's actual input configuration. -/
theorem combined_initial (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (bits : List Bool) :
    Turing.initList (machine ks states symbols p input output main initial z o) bits =
      loadCfg ks states symbols p input output main initial z o false none bits [] [] (fun _ => []) := by
  change Cfg.mk (some (Sum.inl false : Bool ⊕ Fin (p.length+1))) (none,clip states initial) _ =
    Cfg.mk (some (Sum.inl false : Bool ⊕ Fin (p.length+1))) (none,clip states initial)
      (loadStacks ks symbols input bits [] [] (fun _ => []))
  congr 1
  funext k
  cases k with
  | inl b =>
    cases b <;> simp [machine, loadStacks, embedStacks]
    rfl
  | inr j =>
    by_cases h : j = clip ks input <;> simp [machine, loadStacks, embedStacks, Function.update, h]

/-- After the exact loading cost the same machine is in the embedded core
configuration and its next step is a core step. -/
theorem combined_load (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (bits : List Bool) :
    runSteps (machine ks states symbols p input output main initial z o).step (2*bits.length+2)
      (Turing.initList (machine ks states symbols p input output main initial z o) bits) =
      some (embedCfg ks states symbols p.length none [] []
        (coreInit ks states symbols p input output main initial (bits.map (enc symbols z o)) (fun _ => []))) := by
  obtain ⟨v,hscan⟩ := combined_scan_run ks states symbols p input output main initial z o bits [] [] (fun _ => []) none
  simp only [List.append_nil] at hscan
  have hs : runSteps (machine ks states symbols p input output main initial z o).step (bits.length+1)
      (loadCfg ks states symbols p input output main initial z o false none bits [] [] (fun _ => [])) =
        some (loadCfg ks states symbols p input output main initial z o true none [] bits.reverse [] (fun _ => [])) := by
    rw [runSteps_add, hscan]
    change (machine ks states symbols p input output main initial z o).step
      (loadCfg ks states symbols p input output main initial z o false v [] bits.reverse [] (fun _ => [])) = _
    exact combined_scan_nil ks states symbols p input output main initial z o v bits.reverse [] (fun _ => [])
  obtain ⟨w,hrestore⟩ := combined_restore_run ks states symbols p input output main initial z o bits.reverse [] (fun _ => []) none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hrestore
  have hr : runSteps (machine ks states symbols p input output main initial z o).step (bits.length+1)
      (loadCfg ks states symbols p input output main initial z o true none [] bits.reverse [] (fun _ => [])) =
        some (embedCfg ks states symbols p.length none [] []
          (coreInit ks states symbols p input output main initial (bits.map (enc symbols z o)) (fun _ => []))) := by
    rw [runSteps_add, hrestore]
    change (machine ks states symbols p input output main initial z o).step
      (loadCfg ks states symbols p input output main initial z o true w [] [] (bits.map (enc symbols z o)) (fun _ => [])) = _
    exact combined_restore_nil ks states symbols p input output main initial z o w (bits.map (enc symbols z o)) (fun _ => [])
  rw [combined_initial]
  have hn : 2*bits.length+2 = (bits.length+1)+(bits.length+1) := by omega
  rw [hn, runSteps_add, hs]
  exact hr

theorem cfg_ext {K Λ σ : Type} {Γ : K → Type} (c d : Cfg Γ Λ σ)
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c; cases d; simp_all

set_option backward.isDefEq.respectTransparency false in
/-- The combined loader's continuation equals the related numeric start,
not merely its input projection. -/
theorem coreInit_matches_numeric (d : InputData) (p : Program) (output : Nat) (bits : List Bool)
    (hdata : validInputData d = true) :
    ∃ start, buildStart d bits = some start ∧
      coreInit d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        (bits.map (enc d.symbols d.falseSymbol d.trueSymbol)) (fun _ => []) =
        finiteConfig d.stackCount d.states d.symbols p.length start := by
  obtain ⟨start,hs,hstack,hother⟩ := loaded_matches_numeric_start d p bits hdata
  obtain ⟨start',hs',hl,hv⟩ := numeric_start_initial_fields d p bits hdata
  have heq : start = start' := Option.some.inj (hs.symm.trans hs')
  subst start'
  have hd := hdata
  simp only [validInputData, Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨⟨⟨⟨⟨_,_⟩,hi⟩,_⟩,_⟩,_⟩ := hd
  have hidx : (clip d.stackCount d.inputStack).val = d.inputStack := clip_val d.stackCount d.inputStack (by omega)
  refine ⟨start,hs,?_⟩
  apply cfg_ext
  · exact hl.symm
  · exact hv.symm
  · funext k
    by_cases hk : k = clip d.stackCount d.inputStack
    · subst k
      change (Function.update (fun _ : Fin (d.stackCount+1) => []) (clip d.stackCount d.inputStack)
        (bits.map (enc d.symbols d.falseSymbol d.trueSymbol))) (clip d.stackCount d.inputStack) = _
      rw [Function.update_self]
      exact hstack.symm
    · have hk' : k.val ≠ d.inputStack := by
        intro h
        apply hk
        apply Fin.ext
        simpa [hidx] using h
      have hh := hother k hk'
      change (Function.update (fun _ : Fin (d.stackCount+1) => []) (clip d.stackCount d.inputStack)
        (bits.map (enc d.symbols d.falseSymbol d.trueSymbol))) k = _
      rw [Function.update_of_ne hk]
      exact hh.symm

/-- An actual initialized combined machine reaches the exact finite
configuration representing the numeric start. -/
theorem combined_load_numeric (d : InputData) (p : Program) (output : Nat) (bits : List Bool)
    (hdata : validInputData d = true) :
    ∃ start, buildStart d bits = some start ∧
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol).step (2*bits.length+2)
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol) bits) =
        some (embedCfg d.stackCount d.states d.symbols p.length none [] []
          (finiteConfig d.stackCount d.states d.symbols p.length start)) := by
  obtain ⟨start,hs,heq⟩ := coreInit_matches_numeric d p output bits hdata
  refine ⟨start,hs,?_⟩
  rw [← heq]
  exact combined_load d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol bits

set_option backward.isDefEq.respectTransparency false in
/-- Successful checked evaluation yields one initialized combined-machine
run. The input-loading cost is explicit and the core run uses at most its
candidate clock. This does not establish the library's output cleanup. -/
theorem checked_evaluate_combined (d : InputData) (p : Program) (e k z o out : Nat)
    (hdata : validInputData d = true) (hdecode : decodeProgram e = some p)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b) :
    ∃ n ≤ (x.length+2)^k, ∃ c',
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack out d.main d.initialState
        d.falseSymbol d.trueSymbol).step (6*x.length+2+n)
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack out d.main d.initialState
          d.falseSymbol d.trueSymbol) (BitstringEncoding.bitEncode x)) =
        some (embedCfg d.stackCount d.states d.symbols p.length none [] [] c') ∧
      c'.l = none ∧ decodeStack (z,o,(c'.stk (clip d.stackCount out)).map Fin.val) = some b := by
  obtain ⟨start,n,hstart,hn,c',hsteps,hl,hout⟩ :=
    checked_evaluate_finite_run' d p e k z o out hdata hdecode hp x b heval
  obtain ⟨start',hstart',hload⟩ := combined_load_numeric d p out (BitstringEncoding.bitEncode x) hdata
  have eq : start = start' := Option.some.inj (hstart.symm.trans hstart')
  subst start'
  have hlen : (BitstringEncoding.bitEncode x).length = 3*x.length :=
    Shared.ComplexityBridge.bitstring_list_encoded_length x
  rw [hlen] at hload
  have ht : 2*(3*x.length)+2 = 6*x.length+2 := by omega
  rw [ht] at hload
  refine ⟨n,hn,c',?_,hl,hout⟩
  rw [runSteps_add, hload]
  have hc := core_run d.stackCount d.states d.symbols p d.inputStack out d.main d.initialState
    d.falseSymbol d.trueSymbol (finiteConfig d.stackCount d.states d.symbols p.length start) none [] [] n
  rw [hsteps] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- Uniformly for any existing checked decision candidate, success gives one
combined TM2 run from the true initial configuration to a halted label with
matching decoded Boolean output and empty loader stacks. The time is exactly
`6|x|+2+n`, where `n` is at most the candidate's whole-block clock. -/
theorem checked_any_combined (c : Shared.Codes.TM2Candidate.Candidate) (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate c x = some b) :
    let d := inputDataOfRaw c.1.2.2
    ∃ p n, decodeProgram c.1.1 = some p ∧ n ≤ (x.length+2)^c.1.2.1 ∧ ∃ final,
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
        d.falseSymbol d.trueSymbol).step (6*x.length+2+n)
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
          d.falseSymbol d.trueSymbol) (BitstringEncoding.bitEncode x)) = some final ∧
      final.l = none ∧
      decodeStack (c.2.1,c.2.2.1,(final.stk (.inr (clip d.stackCount c.2.2.2))).map Fin.val) = some b ∧
      final.stk (.inl false) = [] ∧ final.stk (.inl true) = [] := by
  let d := inputDataOfRaw c.1.2.2
  have he : Shared.Codes.TM2CheckedCandidate.evaluate
      ((c.1.1,c.1.2.1,inputRaw d),(c.2.1,c.2.2.1,c.2.2.2)) x = some b := by
    simpa [d] using heval
  obtain ⟨hd,p,hp,hvalid⟩ := checked_evaluate_validation d c.1.1 c.1.2.1 c.2.1 c.2.2.1 c.2.2.2 x b he
  obtain ⟨n,hn,q,hrun,hl,hout⟩ := checked_evaluate_combined d p c.1.1 c.1.2.1 c.2.1 c.2.2.1 c.2.2.2 hd hp hvalid x b he
  refine ⟨p,n,hp,hn,embedCfg d.stackCount d.states d.symbols p.length none [] [] q,hrun,?_,?_,?_,?_⟩
  · simp [embedCfg, hl, Option.map] 
  · exact hout
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Generic encoded-input version: any validated numeric run with a
successfully decoded output is reproduced by the combined machine, including
the `2 * bits.length + 2` loading cost. This also applies to pair encodings. -/
theorem combined_numeric_halt (d : InputData) (p : Program) (output z o : Nat)
    (bits : List Bool) (fuel : Nat) (start r : Shared.Codes.TM2StatementExecution.Result) (b : Bool)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (hstart : buildStart d bits = some start) (hrun : run p fuel start = .halted r)
    (he : extractMemory (z,o,output,r.label,r.memory) = some b) :
    ∃ n ≤ fuel, ∃ final,
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol).step (2*bits.length+2+n)
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol) bits) = some final ∧ final.l = none ∧
      decodeStack (z,o,(final.stk (.inr (clip d.stackCount output))).map Fin.val) = some b ∧
      final.stk (.inl false) = [] ∧ final.stk (.inl true) = [] := by
  obtain ⟨start',hs,hvalid⟩ := buildStart_valid d bits p hdata hmain
  have eq : start = start' := Option.some.inj (hstart.symm.trans hs)
  subst start'
  obtain ⟨n,hn,q,hsteps,hl,hout⟩ := finite_run_output d.stackCount d.states d.symbols p
    d.inputStack output d.main d.initialState fuel z o output hp start r hvalid hrun b he
  obtain ⟨start',hs',hload⟩ := combined_load_numeric d p output bits hdata
  have eq : start = start' := Option.some.inj (hstart.symm.trans hs')
  subst start'
  have hc := core_run d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol (finiteConfig d.stackCount d.states d.symbols p.length start) none [] [] n
  rw [hsteps] at hc
  refine ⟨n,hn,embedCfg d.stackCount d.states d.symbols p.length none [] [] q,?_,?_,?_,?_,?_⟩
  · rw [runSteps_add, hload]
    exact hc
  · simp [embedCfg, hl, Option.map]
  · exact hout
  · rfl
  · rfl

end Shared.ComplexityBridge.TM2Combined
