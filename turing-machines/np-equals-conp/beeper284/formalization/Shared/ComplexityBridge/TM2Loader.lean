import Shared.ComplexityBridge.TM2FiniteBoundary

namespace Shared.ComplexityBridge.TM2Loader
open Turing.TM2 Shared.ComplexityBridge.TM2FiniteReverse
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program Shared.Codes.TM2StatementExecution
open Shared.ComplexityBridge.TM2FiniteBoundary

inductive Stack where
  | input | scratch | output
  deriving DecidableEq

inductive Label where
  | scan | restore | done
  deriving DecidableEq

instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro x; cases x <;> simp)
instance : Fintype Label := Fintype.ofList [.scan,.restore,.done] (by intro x; cases x <;> simp)

def Alphabet (symbols : Nat) : Stack → Type
  | .input => Bool
  | .scratch => Bool
  | .output => Fin (symbols+1)

def enc (symbols z o : Nat) (b : Bool) : Fin (symbols+1) :=
  clip symbols (inputBit z o b)

def program (symbols z o : Nat) : Label → Stmt (Alphabet symbols) Label (Option Bool)
  | .scan => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan)))
        (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun v => enc symbols z o (v.getD false)) (.goto (fun _ => .restore)))
        (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)

def loader (symbols z o : Nat) : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet symbols
  Λ := Label
  main := .scan
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program symbols z o

def stackVals (symbols : Nat) (a b : List Bool) (c : List (Fin (symbols+1))) :
    (k : Stack) → List (Alphabet symbols k)
  | .input => a
  | .scratch => b
  | .output => c

def config (symbols : Nat) (l : Label) (v : Option Bool) (a b : List Bool)
    (c : List (Fin (symbols+1))) : (loader symbols z o).Cfg :=
  ⟨some l,v,stackVals symbols a b c⟩

theorem scan_cons (symbols z o : Nat) (v : Option Bool) (x : Bool) (xs ys : List Bool)
    (os : List (Fin (symbols+1))) :
    (loader symbols z o).step (config symbols .scan v (x::xs) ys os) =
      some (config symbols .scan (some x) xs (x::ys) os) := by
  change some (Turing.TM2.Cfg.mk (some Label.scan) (some x)
    (Function.update (Function.update (stackVals symbols (x::xs) ys os) Stack.input xs)
      Stack.scratch (x::ys))) = some (Turing.TM2.Cfg.mk (some Label.scan) (some x)
        (stackVals symbols xs (x::ys) os))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals, Function.update] <;> rfl

theorem scan_nil (symbols z o : Nat) (v : Option Bool) (ys : List Bool)
    (os : List (Fin (symbols+1))) :
    (loader symbols z o).step (config symbols .scan v [] ys os) =
      some (config symbols .restore none [] ys os) := by
  change some (Turing.TM2.Cfg.mk (some Label.restore) none
    (Function.update (stackVals symbols [] ys os) Stack.input [])) =
      some (Turing.TM2.Cfg.mk (some Label.restore) none (stackVals symbols [] ys os))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals, Function.update] <;> rfl

theorem restore_cons (symbols z o : Nat) (v : Option Bool) (x : Bool) (xs : List Bool)
    (os : List (Fin (symbols+1))) :
    (loader symbols z o).step (config symbols .restore v [] (x::xs) os) =
      some (config symbols .restore (some x) [] xs (enc symbols z o x::os)) := by
  change some (Turing.TM2.Cfg.mk (some Label.restore) (some x)
    (Function.update (Function.update (stackVals symbols [] (x::xs) os) Stack.scratch xs)
      Stack.output (enc symbols z o x::os))) =
        some (Turing.TM2.Cfg.mk (some Label.restore) (some x)
          (stackVals symbols [] xs (enc symbols z o x::os)))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals, Function.update] <;> rfl

theorem restore_nil (symbols z o : Nat) (v : Option Bool) (os : List (Fin (symbols+1))) :
    (loader symbols z o).step (config symbols .restore v [] [] os) =
      some (config symbols .done none [] [] os) := by
  change some (Turing.TM2.Cfg.mk (some Label.done) none
    (Function.update (stackVals symbols [] [] os) Stack.scratch [])) =
      some (Turing.TM2.Cfg.mk (some Label.done) none (stackVals symbols [] [] os))
  congr 1
  congr 1
  funext k
  cases k <;> simp [stackVals, Function.update] <;> rfl

/-- The first pass reverses the input onto scratch, one block per bit. -/
theorem scan_run (symbols z o : Nat) (xs ys : List Bool)
    (os : List (Fin (symbols+1))) (v : Option Bool) :
    ∃ v', runSteps (loader symbols z o).step xs.length (config symbols .scan v xs ys os) =
      some (config symbols .scan v' [] (xs.reverse ++ ys) os) := by
  induction xs generalizing ys v with
  | nil => exact ⟨v, by simp [runSteps]⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih (x::ys) (some x)
    refine ⟨v', ?_⟩
    rw [List.length_cons, runSteps_front, scan_cons]
    simpa [List.reverse_cons, List.append_assoc] using hv

/-- The second pass restores the original order while mapping symbols. -/
theorem restore_run (symbols z o : Nat) (xs : List Bool)
    (os : List (Fin (symbols+1))) (v : Option Bool) :
    ∃ v', runSteps (loader symbols z o).step xs.length (config symbols .restore v [] xs os) =
      some (config symbols .restore v' [] [] (xs.reverse.map (enc symbols z o) ++ os)) := by
  induction xs generalizing os v with
  | nil => exact ⟨v, by simp [runSteps]⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih (enc symbols z o x::os) (some x)
    refine ⟨v', ?_⟩
    rw [List.length_cons, runSteps_front, restore_cons]
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using hv

/-- The configuration used by the first pass is the library's actual initial
configuration, with an ordinary Boolean input alphabet. -/
theorem initial_eq (symbols z o : Nat) (bits : List Bool) :
    Turing.initList (loader symbols z o) bits = config symbols .scan none bits [] [] := by
  change Turing.TM2.Cfg.mk (some Label.scan) none _ =
    Turing.TM2.Cfg.mk (some Label.scan) none (stackVals symbols bits [] [])
  congr 1
  funext k
  cases k <;> simp [loader, stackVals] <;> rfl

/-- Starting at the actual `initList`, loading reaches the continuation label
in exactly `2 * bits.length + 2` whole TM2 statement blocks. -/
theorem load_correct (symbols z o : Nat) (bits : List Bool) :
    runSteps (loader symbols z o).step (2*bits.length+2) (Turing.initList (loader symbols z o) bits) =
      some (config symbols .done none [] [] (bits.map (enc symbols z o))) := by
  obtain ⟨v,hscan⟩ := scan_run symbols z o bits [] [] none
  simp only [List.append_nil] at hscan
  have hs : runSteps (loader symbols z o).step (bits.length+1)
      (config symbols .scan none bits [] []) =
        some (config symbols .restore none [] bits.reverse []) := by
    rw [runSteps_add, hscan]
    change (loader symbols z o).step (config symbols .scan v [] bits.reverse []) = _
    exact scan_nil symbols z o v bits.reverse []
  obtain ⟨w,hrestore⟩ := restore_run symbols z o bits.reverse [] none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hrestore
  have hr : runSteps (loader symbols z o).step (bits.length+1)
      (config symbols .restore none [] bits.reverse []) =
        some (config symbols .done none [] [] (bits.map (enc symbols z o))) := by
    rw [runSteps_add, hrestore]
    change (loader symbols z o).step (config symbols .restore w [] [] (bits.map (enc symbols z o))) = _
    exact restore_nil symbols z o w (bits.map (enc symbols z o))
  rw [initial_eq]
  have hn : 2*bits.length+2 = (bits.length+1)+(bits.length+1) := by omega
  rw [hn, runSteps_add, hs]
  exact hr

theorem stackFn_empty (n k : Nat) : stackFn (List.replicate n []) k = [] := by
  simp [stackFn]

/-- The loader output is exactly the input stack of the related numeric start;
all other core stacks are empty, including the extra default stack. -/
theorem loaded_matches_numeric_start (d : InputData) (p : Program) (bits : List Bool)
    (hdata : validInputData d = true) :
    ∃ start, buildStart d bits = some start ∧
      (finiteConfig d.stackCount d.states d.symbols p.length start).stk (clip d.stackCount d.inputStack) =
        bits.map (enc d.symbols d.falseSymbol d.trueSymbol) ∧
      ∀ k : Fin (d.stackCount+1), k.val ≠ d.inputStack →
        (finiteConfig d.stackCount d.states d.symbols p.length start).stk k = [] := by
  have hd := hdata
  simp only [validInputData, Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨⟨⟨⟨⟨_,_⟩,hi⟩,_⟩,_⟩,_⟩ := hd
  let start : Result := ⟨some d.main,d.initialState,
    (List.replicate d.stackCount []).set d.inputStack (bits.map (inputBit d.falseSymbol d.trueSymbol))⟩
  have hi' : d.inputStack < (List.replicate d.stackCount ([] : List Nat)).length := by simpa using hi
  have hidx : (clip d.stackCount d.inputStack).val = d.inputStack := clip_val d.stackCount d.inputStack (by omega)
  refine ⟨start, by simp [buildStart, hdata, start], ?_, ?_⟩
  · simp only [finiteConfig, start, hidx, stackFn_set _ _ _ hi', Function.update_self, List.map_map]
    rfl
  · intro k hk
    simp only [finiteConfig, start, stackFn_set _ _ _ hi', Function.update_of_ne hk, stackFn_empty, List.map_nil]

/-- The corresponding numeric start uses the core machine's actual main
label and initial control state. -/
theorem numeric_start_initial_fields (d : InputData) (p : Program) (bits : List Bool)
    (hdata : validInputData d = true) :
    ∃ start, buildStart d bits = some start ∧
      (finiteConfig d.stackCount d.states d.symbols p.length start).l =
        some (finiteCore d.stackCount d.states d.symbols p d.inputStack 0 d.main d.initialState).main ∧
      (finiteConfig d.stackCount d.states d.symbols p.length start).var =
        (finiteCore d.stackCount d.states d.symbols p d.inputStack 0 d.main d.initialState).initialState := by
  refine ⟨⟨some d.main,d.initialState,
    (List.replicate d.stackCount []).set d.inputStack (bits.map (inputBit d.falseSymbol d.trueSymbol))⟩, ?_, ?_, ?_⟩
  · simp [buildStart, hdata]
  · rfl
  · rfl

/-- The library encoding of a decision input incurs exactly `6|x|+2`
loader blocks. -/
theorem decision_load_correct (symbols z o : Nat) (x : List Bool) :
    runSteps (loader symbols z o).step (6*x.length+2)
      (Turing.initList (loader symbols z o) (BitstringEncoding.bitEncode x)) =
      some (config symbols .done none [] [] ((BitstringEncoding.bitEncode x).map (enc symbols z o))) := by
  have h := load_correct symbols z o (BitstringEncoding.bitEncode x)
  rw [Shared.ComplexityBridge.bitstring_list_encoded_length] at h
  have ht : 2*(3*x.length)+2 = 6*x.length+2 := by omega
  rw [ht] at h
  exact h

/-- The pair encoding incurs exactly `12|x|+6|w|+4` loader blocks. -/
theorem pair_load_correct (symbols z o : Nat) (x w : List Bool) :
    runSteps (loader symbols z o).step (12*x.length+6*w.length+4)
      (Turing.initList (loader symbols z o) (BitstringEncoding.bitEncode (x,w))) =
      some (config symbols .done none [] [] ((BitstringEncoding.bitEncode (x,w)).map (enc symbols z o))) := by
  have h := load_correct symbols z o (BitstringEncoding.bitEncode (x,w))
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length] at h
  have ht : 2*(6*x.length+1+3*w.length)+2 = 12*x.length+6*w.length+4 := by omega
  rw [ht] at h
  exact h

/-- A concrete loader run reaches data matching the finite core's related
numeric start, including all stack, label and state components. The loader
and core are still separate machines; this does not itself splice their runs. -/
theorem loader_matches_core_start (d : InputData) (p : Program) (bits : List Bool)
    (hdata : validInputData d = true) :
    ∃ start, buildStart d bits = some start ∧
      runSteps (loader d.symbols d.falseSymbol d.trueSymbol).step (2*bits.length+2)
        (Turing.initList (loader d.symbols d.falseSymbol d.trueSymbol) bits) =
          some (config d.symbols .done none [] [] (bits.map (enc d.symbols d.falseSymbol d.trueSymbol))) ∧
      (finiteConfig d.stackCount d.states d.symbols p.length start).stk (clip d.stackCount d.inputStack) =
        bits.map (enc d.symbols d.falseSymbol d.trueSymbol) ∧
      (∀ k : Fin (d.stackCount+1), k.val ≠ d.inputStack →
        (finiteConfig d.stackCount d.states d.symbols p.length start).stk k = []) ∧
      (finiteConfig d.stackCount d.states d.symbols p.length start).l =
        some (finiteCore d.stackCount d.states d.symbols p d.inputStack 0 d.main d.initialState).main ∧
      (finiteConfig d.stackCount d.states d.symbols p.length start).var =
        (finiteCore d.stackCount d.states d.symbols p d.inputStack 0 d.main d.initialState).initialState := by
  obtain ⟨start,hs,hstack,hother⟩ := loaded_matches_numeric_start d p bits hdata
  obtain ⟨start',hs',hl,hv⟩ := numeric_start_initial_fields d p bits hdata
  have eq : start = start' := Option.some.inj (hs.symm.trans hs')
  subst start'
  exact ⟨start,hs,load_correct d.symbols d.falseSymbol d.trueSymbol bits,hstack,hother,hl,hv⟩

example : (runSteps (loader 2 0 1).step 2 (Turing.initList (loader 2 0 1) [])).map
    (fun c => c.l) = some (some .done) := by
  have h := load_correct 2 0 1 []
  have hh := congrArg (Option.map (fun c => c.l)) h
  change (runSteps (loader 2 0 1).step 2 (Turing.initList (loader 2 0 1) [])).map (fun c => c.l) = some (some .done) at hh
  exact hh
example : (runSteps (loader 2 0 1).step 6 (Turing.initList (loader 2 0 1) [false,true])).map
    (fun c => c.stk .output) = some [clip 2 0,clip 2 1] := by
  have h := load_correct 2 0 1 [false,true]
  have hh := congrArg (Option.map (fun c => c.stk .output)) h
  change (runSteps (loader 2 0 1).step 6 (Turing.initList (loader 2 0 1) [false,true])).map (fun c => c.stk .output) = some [clip 2 0, clip 2 1] at hh
  exact hh

end Shared.ComplexityBridge.TM2Loader
