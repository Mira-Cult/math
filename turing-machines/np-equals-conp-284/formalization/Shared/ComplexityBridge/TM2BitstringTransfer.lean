import Shared.ComplexityBridge.TM2BitstringOutput
import Shared.ComplexityBridge.TM2StackBound

/-! Transfer an arbitrary finite numeric output stack to a Boolean output
stack in its original order. This standalone finite TM2 clears its own
scratch and source-output stack; cleanup of the other core stacks is separate. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BitstringTransfer
open Turing.TM2 Shared.ComplexityBridge.TM2Combined Shared.ComplexityBridge.TM2FiniteReverse
open Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2BitstringOutput

inductive Label where | scan | restore deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.scan,.restore] (by intro l; cases l <;> simp)

abbrev State (symbols : Nat) := Option (Fin (symbols+1)) × Option Bool

def program (ks symbols output one : Nat) : Label → Stmt (Alphabet ks symbols) Label (State symbols)
  | .scan => .pop (.inr (clip ks output)) (fun _ x => (x,none))
      (.branch (fun v => v.1.isSome)
        (.push (.inl false) (fun v => (v.1.map (fun x => x.val == one)).getD false)
          (.goto (fun _ => .scan)))
        (.goto (fun _ => .restore)))
  | .restore => .pop (.inl false) (fun _ x => (none,x))
      (.branch (fun v => v.2.isSome)
        (.push (.inl true) (fun v => v.2.getD false) (.goto (fun _ => .restore)))
        (.load (fun _ => (none,none)) .halt))

def machine (ks symbols output one : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Label
  main := .scan
  σ := State symbols
  initialState := (none,none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks symbols output one

def cfg (ks symbols output one : Nat) (l : Option Label) (v : State symbols)
    (scratch result : List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks symbols output one).Cfg :=
  ⟨l,v,embedStacks ks symbols scratch result S⟩

def sourceIndex (ks output : Nat) : Fin (ks+1) := clip ks output

theorem scan_cons (ks symbols output one : Nat) (v : State symbols)
    (scratch result : List Bool) (S : Fin (ks+1) → List (Fin (symbols+1)))
    (x : Fin (symbols+1)) (xs : List (Fin (symbols+1))) :
    (machine ks symbols output one).step
      (cfg ks symbols output one (some .scan) v scratch result
        (Function.update S (sourceIndex ks output) (x::xs))) =
      some (cfg ks symbols output one (some .scan) (some x,none)
        ((x.val == one)::scratch) result (Function.update S (sourceIndex ks output) xs)) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,stepAux,
    sourceIndex,embedStacks,Function.update_self,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.map_some,Option.getD_some]
  congr 1
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [embedStacks,Function.update]
  | inr j =>
    by_cases h : j = clip ks output
    · subst j; simp [embedStacks,Function.update]
    · simp [embedStacks,Function.update,h]

theorem scan_nil (ks symbols output one : Nat) (v : State symbols)
    (scratch result : List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks symbols output one).step
      (cfg ks symbols output one (some .scan) v scratch result
        (Function.update S (sourceIndex ks output) [])) =
      some (cfg ks symbols output one (some .restore) (none,none) scratch result
        (Function.update S (sourceIndex ks output) [])) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cfg,program,stepAux,
    sourceIndex,embedStacks,Function.update_self,List.head?_nil,List.tail_nil,Option.isSome_none,
    Bool.cond_false]
  congr 1
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [embedStacks,Function.update]
  | inr j =>
    by_cases h : j = clip ks output
    · subst j; simp [embedStacks,Function.update]
    · simp [embedStacks,Function.update,h]

theorem restore_cons (ks symbols output one : Nat) (v : State symbols)
    (scratch result : List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) (b : Bool) :
    (machine ks symbols output one).step
      (cfg ks symbols output one (some .restore) v (b::scratch) result S) =
      some (cfg ks symbols output one (some .restore) (none,some b) scratch (b::result) S) := by
  change some (Cfg.mk (some Label.restore) (none,some b)
    (Function.update (Function.update (embedStacks ks symbols (b::scratch) result S) (.inl false) scratch)
      (.inl true) (b::result))) = _
  congr 1
  congr 1
  funext k
  cases k with
  | inl x => cases x <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

theorem restore_nil (ks symbols output one : Nat) (v : State symbols)
    (result : List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks symbols output one).step (cfg ks symbols output one (some .restore) v [] result S) =
      some (cfg ks symbols output one none (none,none) [] result S) := by
  change some (Cfg.mk none (none,none) (Function.update (embedStacks ks symbols [] result S) (.inl false) [])) = _
  congr 1
  congr 1
  funext k
  cases k with
  | inl x => cases x <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

/-- The first pass reverses the decoded output onto scratch. -/
theorem scan_run (ks symbols output one : Nat) (xs : List (Fin (symbols+1)))
    (scratch result : List Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) (v : State symbols) :
    ∃ v', runSteps (machine ks symbols output one).step xs.length
      (cfg ks symbols output one (some .scan) v scratch result
        (Function.update S (sourceIndex ks output) xs)) =
      some (cfg ks symbols output one (some .scan) v'
        ((xs.map (fun x => x.val == one)).reverse ++ scratch) result
        (Function.update S (sourceIndex ks output) [])) := by
  induction xs generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih ((x.val == one)::scratch) (some x,none)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,scan_cons]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using hv

/-- The second pass restores the original order and empties scratch. -/
theorem restore_run (ks symbols output one : Nat) (xs result : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (v : State symbols) :
    ∃ v', runSteps (machine ks symbols output one).step xs.length
      (cfg ks symbols output one (some .restore) v xs result S) =
      some (cfg ks symbols output one (some .restore) v' [] (xs.reverse++result) S) := by
  induction xs generalizing result v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b xs ih =>
    obtain ⟨v',hv⟩ := ih (b::result) (none,some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using hv

/-- The exact transfer requires `2 * length + 2` blocks, even for empty
output; all other numeric stacks remain unchanged. -/
theorem transfer (ks symbols output one : Nat) (xs : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) (v : State symbols) :
    runSteps (machine ks symbols output one).step (2*xs.length+2)
      (cfg ks symbols output one (some .scan) v [] []
        (Function.update S (sourceIndex ks output) xs)) =
      some (cfg ks symbols output one none (none,none) []
        (xs.map (fun x => x.val == one)) (Function.update S (sourceIndex ks output) [])) := by
  obtain ⟨w,hs⟩ := scan_run ks symbols output one xs [] [] S v
  simp only [List.append_nil] at hs
  have hscan : runSteps (machine ks symbols output one).step (xs.length+1)
      (cfg ks symbols output one (some .scan) v [] [] (Function.update S (sourceIndex ks output) xs)) =
      some (cfg ks symbols output one (some .restore) (none,none)
        (xs.map (fun x => x.val == one)).reverse [] (Function.update S (sourceIndex ks output) [])) := by
    rw [runSteps_add,hs]
    exact scan_nil ks symbols output one w _ _ S
  obtain ⟨u,hr⟩ := restore_run ks symbols output one (xs.map (fun x => x.val == one)).reverse []
    (Function.update S (sourceIndex ks output) []) (none,none)
  simp only [List.length_reverse,List.length_map,List.reverse_reverse,List.append_nil] at hr
  rw [show 2*xs.length+2 = (xs.length+1)+(xs.length+1) by omega,runSteps_add,hscan]
  change runSteps (machine ks symbols output one).step (xs.length+1)
    (cfg ks symbols output one (some .restore) (none,none)
      (xs.map (fun x => x.val == one)).reverse [] (Function.update S (sourceIndex ks output) [])) = _
  rw [runSteps_add,hr]
  exact restore_nil ks symbols output one u _ _

/-- A successful strict decoder returns exactly the elementwise Boolean map. -/
theorem decode_value (z o : Nat) (xs : List (Fin (symbols+1))) (bits : List Bool)
    (h : decodeStack (z,o,xs.map Fin.val) = some bits) :
    xs.map (fun x => x.val == o) = bits := by
  unfold decodeStack at h
  split at h
  · contradiction
  · split at h
    · have he := Option.some.inj h
      simpa [decodedBit,List.map_map,Function.comp_def] using he
    · contradiction

/-- On a valid encoded output stack, the finite machine emits exactly the
strict decoder's result, in order. -/
theorem transfer_decoded (ks symbols output z o : Nat) (xs : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) (v : State symbols) (bits : List Bool)
    (hdecode : decodeStack (z,o,xs.map Fin.val) = some bits) :
    runSteps (machine ks symbols output o).step (2*xs.length+2)
      (cfg ks symbols output o (some .scan) v [] []
        (Function.update S (sourceIndex ks output) xs)) =
      some (cfg ks symbols output o none (none,none) [] bits
        (Function.update S (sourceIndex ks output) [])) := by
  have he := decode_value z o xs bits hdecode
  simpa [he] using transfer ks symbols output o xs S v

/-- Strict numeric extraction transfers through the validated finite-core
simulation. The numeric output-stack index must exist, including for empty
outputs. -/
theorem extract_from_related {ks states symbols labels z o out : Nat}
    (r : Shared.Codes.TM2StatementExecution.Result)
    (c : Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1)))
    (hr : Shared.Codes.TM2StatementValidation.resultValid ks states symbols labels r)
    (hrel : CfgRel ks states symbols labels c (Shared.Codes.TM2StatementExecution.erase r))
    (bits : List Bool) (he : extractMemory (z,o,out,r.label,r.memory) = some bits) :
    c.l = none ∧ decodeStack (z,o,(c.stk (clip ks out)).map Fin.val) = some bits := by
  have hl : r.label = none := by
    unfold extractMemory at he
    cases h : r.label <;> simp [h] at he ⊢
  have hindex : out < r.memory.length := by
    unfold extractMemory at he
    rw [hl] at he
    by_contra h
    simp [h] at he
  have hout : out < ks := by
    have hlen := hr.2.1.1
    omega
  have hidx : (clip ks out).val = out := clip_val ks out (by omega)
  have hstack := hrel.2.2 (clip ks out)
  rw [hidx] at hstack
  change Shared.Codes.TM2StatementExecution.stackFn r.memory out = (c.stk (clip ks out)).map Fin.val at hstack
  have hc : c.l = none := by
    have h := hrel.1
    change r.label = c.l.map Fin.val at h
    rw [hl] at h
    cases hx : c.l <;> simp [hx] at h ⊢
  refine ⟨hc,?_⟩
  unfold extractMemory at he
  simp only [hl,Option.isSome_none,Bool.false_eq_true,if_false,hindex,if_true,hstack] at he
  exact he

/-- An actual halted numeric run yields a related finite-core run and a
separate finite transfer of its entire decoded output. The output is bounded
by the source input length plus the fixed program's block depth times fuel.
This does not yet combine the machines or clear the other stacks. -/
theorem numeric_run_then_transfer
    (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (p : Shared.Codes.TM2Program.Program) (output z o : Nat) (input : List Bool) (fuel : Nat)
    (start r : Shared.Codes.TM2StatementExecution.Result) (bits : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true) (hmain : d.main < p.length)
    (hp : Shared.Codes.TM2Program.programValid p d.stackCount d.states d.symbols = true)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d input = some start)
    (hrun : Shared.Codes.TM2Program.run p fuel start = .halted r)
    (he : extractMemory (z,o,output,r.label,r.memory) = some bits) :
    ∃ n ≤ fuel, ∃ c',
      runSteps (finiteCore d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState).step n
        (finiteConfig d.stackCount d.states d.symbols p.length start) = some c' ∧
      c'.l = none ∧ ∃ t ≤ 2*(input.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p)+2,
        runSteps (machine d.stackCount d.symbols output o).step t
          (cfg d.stackCount d.symbols output o (some .scan) (none,none) [] [] c'.stk) =
        some (cfg d.stackCount d.symbols output o none (none,none) [] bits
          (Function.update c'.stk (clip d.stackCount output) [])) := by
  obtain ⟨start',hs,hv⟩ := Shared.ComplexityBridge.TM2FiniteBoundary.buildStart_valid d input p hdata hmain
  have hs' : start' = start := by rw [hstart] at hs; exact Option.some.inj hs.symm
  subst start'
  have hrvalid := Shared.Codes.TM2Program.run_safe p d.stackCount d.states d.symbols hp fuel start hv
  rw [hrun] at hrvalid
  have hcore := finite_run_from_config d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    hp fuel start hv
  rw [hrun] at hcore
  obtain ⟨n,hn,c',hsteps,hrel,hhalt⟩ := hcore
  have hout := extract_from_related r c' hrvalid.1 hrel bits he
  have hstack := Shared.ComplexityBridge.TM2StackBound.run_from_input_bound d input p fuel start hstart
  rw [hrun] at hstack
  have hbound := Shared.ComplexityBridge.TM2StackBound.related_stack_bound d.stackCount d.states d.symbols p.length
    c' r hrel (input.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p) hstack
  let xs := c'.stk (clip d.stackCount output)
  have htransfer := transfer_decoded d.stackCount d.symbols output z o xs c'.stk (none,none) bits hout.2
  have hup : Function.update c'.stk (sourceIndex d.stackCount output) xs = c'.stk := by
    exact Function.update_eq_self _ _
  rw [hup] at htransfer
  have hlen : xs.length ≤ input.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p :=
    hbound (clip d.stackCount output)
  refine ⟨n,hn,c',hsteps,hout.1,2*xs.length+2,by omega,?_⟩
  exact htransfer

/-- The preceding finite-core/transfer result also starts from mathlib's
actual input configuration: its loader is charged `2 * input.length + 2`
blocks. The transfer remains a separate run with an explicit handoff. -/
theorem loaded_numeric_run_then_transfer
    (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (p : Shared.Codes.TM2Program.Program) (output z o : Nat) (input : List Bool) (fuel : Nat)
    (start r : Shared.Codes.TM2StatementExecution.Result) (bits : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true) (hmain : d.main < p.length)
    (hp : Shared.Codes.TM2Program.programValid p d.stackCount d.states d.symbols = true)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d input = some start)
    (hrun : Shared.Codes.TM2Program.run p fuel start = .halted r)
    (he : extractMemory (z,o,output,r.label,r.memory) = some bits) :
    ∃ n ≤ fuel, ∃ c',
      runSteps (Shared.ComplexityBridge.TM2Combined.machine d.stackCount d.states d.symbols p
        d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step
        (2*input.length+2+n)
        (Turing.initList (Shared.ComplexityBridge.TM2Combined.machine d.stackCount d.states d.symbols p
          d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol) input) =
        some (embedCfg d.stackCount d.states d.symbols p.length none [] [] c') ∧
      c'.l = none ∧ ∃ t ≤ 2*(input.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p)+2,
        runSteps (machine d.stackCount d.symbols output o).step t
          (cfg d.stackCount d.symbols output o (some .scan) (none,none) [] [] c'.stk) =
        some (cfg d.stackCount d.symbols output o none (none,none) [] bits
          (Function.update c'.stk (clip d.stackCount output) [])) := by
  obtain ⟨n,hn,c',hsteps,hl,t,ht,htransfer⟩ :=
    numeric_run_then_transfer d p output z o input fuel start r bits hdata hmain hp hstart hrun he
  obtain ⟨start',hs,hload⟩ := Shared.ComplexityBridge.TM2Combined.combined_load_numeric d p output input hdata
  have eq : start = start' := Option.some.inj (hstart.symm.trans hs)
  subst start'
  have hsim := Shared.ComplexityBridge.TM2Combined.core_run d.stackCount d.states d.symbols p
    d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol
    (finiteConfig d.stackCount d.states d.symbols p.length start) none [] [] n
  rw [hsteps] at hsim
  refine ⟨n,hn,c',?_,hl,t,ht,htransfer⟩
  rw [runSteps_add,hload]
  exact hsim

namespace Fixtures

def core : Fin 2 → List (Fin 3) := fun k => if k.val = 0 then [] else [2]

example : runSteps (machine 1 2 0 1).step 2
    (cfg 1 2 0 1 (some .scan) (none,none) [] []
      (Function.update core (sourceIndex 1 0) [])) =
    some (cfg 1 2 0 1 none (none,none) [] []
      (Function.update core (sourceIndex 1 0) [])) := by
  simpa using transfer 1 2 0 1 [] core (none,none)

example : runSteps (machine 1 2 0 1).step 8
    (cfg 1 2 0 1 (some .scan) (none,none) [] []
      (Function.update core (sourceIndex 1 0) [1,0,1])) =
    some (cfg 1 2 0 1 none (none,none) [] [true,false,true]
      (Function.update core (sourceIndex 1 0) [])) := by
  simpa using transfer_decoded 1 2 0 0 1 [1,0,1] core (none,none) [true,false,true] (by decide)

example : (Function.update core (sourceIndex 1 0) []) ⟨1,by decide⟩ = [2] := by decide

end Fixtures
end Shared.ComplexityBridge.TM2BitstringTransfer
