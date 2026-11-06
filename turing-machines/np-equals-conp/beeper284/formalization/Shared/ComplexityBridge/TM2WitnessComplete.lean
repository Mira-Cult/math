import Shared.ComplexityBridge.TM2WitnessInput

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2WitnessComplete
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Load := Shared.ComplexityBridge.TM2WitnessInput.machine
abbrev Output := Shared.ComplexityBridge.TM2WitnessOutput.machine
abbrev Key := Shared.ComplexityBridge.TM2WitnessLookup.Key
abbrev LoadLabel := Shared.ComplexityBridge.TM2WitnessInput.Label
abbrev OutputLabel := Shared.ComplexityBridge.TM2WitnessOutput.Label
abbrev OutputState := Shared.ComplexityBridge.TM2WitnessOutput.State
abbrev Label := Unit ⊕ (LoadLabel ⊕ OutputLabel)
abbrev State := Option Bool ⊕ OutputState

def loadState : State → Option Bool | .inl v => v | _ => none
def outputState : State → OutputState | .inr v => v | _ => Output.initialState

def swap : Key → Key | .vars => .query | .query => .vars | k => k
@[simp] theorem swap_swap (k : Key) : swap (swap k) = k := by cases k <;> rfl
def swapStacks (S : Key → List Bool) : Key → List Bool := fun k => S (swap k)
@[simp] theorem swapStacks_apply (S : Key → List Bool) (j : Key) : swapStacks S (swap j) = S j := by simp [swapStacks]
theorem swap_update (S : Key → List Bool) (j : Key) (xs : List Bool) :
    swapStacks (Function.update S j xs) = Function.update (swapStacks S) (swap j) xs := by
  funext k; cases j <;> cases k <;> simp [swapStacks,swap,Function.update]

def loadEmbed (q : Load.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),.inl q.var,q.stk⟩
def outEmbed (q : Output.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inr l)),.inr q.var,swapStacks q.stk⟩

def liftLoad : Stmt (fun _ : Key => Bool) LoadLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push j (fun v => f (loadState v)) (liftLoad q)
  | .peek j f q => .peek j (fun v h => .inl (f (loadState v) h)) (liftLoad q)
  | .pop j f q => .pop j (fun v h => .inl (f (loadState v) h)) (liftLoad q)
  | .load f q => .load (fun v => .inl (f (loadState v))) (liftLoad q)
  | .branch f q r => .branch (fun v => f (loadState v)) (liftLoad q) (liftLoad r)
  | .goto f => .goto (fun v => .inr (.inl (f (loadState v))))
  | .halt => .halt

def liftOutput : Stmt (fun _ : Key => Bool) OutputLabel OutputState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (swap j) (fun v => f (outputState v)) (liftOutput q)
  | .peek j f q => .peek (swap j) (fun v h => .inr (f (outputState v) h)) (liftOutput q)
  | .pop j f q => .pop (swap j) (fun v h => .inr (f (outputState v) h)) (liftOutput q)
  | .load f q => .load (fun v => .inr (f (outputState v))) (liftOutput q)
  | .branch f q r => .branch (fun v => f (outputState v)) (liftOutput q) (liftOutput r)
  | .goto f => .goto (fun v => .inr (.inr (f (outputState v))))
  | .halt => .halt

theorem liftLoad_aux (q : Load.Stmt) (v : Option Bool) (S : Key → List Bool) :
    stepAux (liftLoad q) (.inl v) S = loadEmbed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftLoad,stepAux,loadState,h,ihq,ihr]

theorem liftOutput_aux (q : Output.Stmt) (v : OutputState) (S : Key → List Bool) :
    stepAux (liftOutput q) (.inr v) (swapStacks S) = outEmbed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftOutput,stepAux,outputState,swapStacks_apply]
    rw [← swap_update S j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftOutput,stepAux,outputState,swapStacks_apply]; exact ih _ _
  | pop j f q ih =>
    simp only [liftOutput,stepAux,outputState,swapStacks_apply]
    rw [← swap_update S j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftOutput,stepAux,outputState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl () => .load (fun _ => .inl none) (.goto (fun _ => .inr (.inl (.inl (false,.x0)))))
  | .inr (.inl (.inr ())) => .load (fun _ => .inr Output.initialState)
      (.goto (fun _ => .inr (.inr Output.main)))
  | .inr (.inl l) => liftLoad (Shared.ComplexityBridge.TM2WitnessInput.program l)
  | .inr (.inr l) => liftOutput (Shared.ComplexityBridge.TM2WitnessOutput.program l)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .vars
  k₁ := .query
  Γ := fun _ => Bool
  Λ := Label
  main := .inl ()
  σ := State
  initialState := .inr Output.initialState
  m := program

def loadTerminal (q : Load.Cfg) : Prop := q.l = some (.inr ())
noncomputable instance : DecidablePred loadTerminal := fun _ => Classical.propDecidable _
theorem load_stable (q : Load.Cfg) (h : loadTerminal q) : Load.step q = some q := by
  cases q with
  | mk l v S => change l = some (.inr ()) at h; subst l; rfl

theorem load_step (q : Load.Cfg) (h : ¬ loadTerminal q) :
    machine.step (loadEmbed q) = (Load.step q).map loadEmbed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inr u => cases u; exact False.elim (h rfl)
      | inl p =>
        change some (stepAux (liftLoad (Shared.ComplexityBridge.TM2WitnessInput.program (.inl p))) (.inl v) S) = _
        rw [liftLoad_aux]; rfl

theorem out_step (q : Output.Cfg) : machine.step (outEmbed q) = (Output.step q).map outEmbed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftOutput (Shared.ComplexityBridge.TM2WitnessOutput.program l)) (.inr v) (swapStacks S)) = _
      rw [liftOutput_aux]; rfl

theorem out_run (q : Output.Cfg) (n : Nat) :
    runSteps machine.step n (outEmbed q) = (runSteps Output.step n q).map outEmbed := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,out_step]
    cases h : Output.step q with
    | none => rfl
    | some q' => exact ih q'

theorem startup (bits : List Bool) :
    machine.step (Turing.initList machine bits) = some (loadEmbed (Turing.initList Load bits)) := by
  rfl

theorem dispatch (first witness query : List Bool) :
    machine.step (loadEmbed (Shared.ComplexityBridge.TM2WitnessInput.finalCfg first witness query)) =
      some (outEmbed (Shared.ComplexityBridge.TM2WitnessOutput.embed
        (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none first witness query [] [] []))) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> rfl

theorem out_halt (b : Bool) : outEmbed (Turing.haltList Output [b]) = Turing.haltList machine [b] := by
  change Cfg.mk none (Sum.inr Output.initialState : State) _ = Cfg.mk none (Sum.inr Output.initialState : State) _
  congr 1; funext k; cases k <;> simp [outEmbed,swapStacks,swap,Turing.haltList,machine,Output,Shared.ComplexityBridge.TM2WitnessOutput.machine] <;> rfl

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 4*Polynomial.X + Polynomial.C 8 + Shared.ComplexityBridge.TM2WitnessOutput.timePolynomial

/-- The explicit external encoding contains the framed names and a separately
encoded witness/query pair. Every initialization, lookup and cleanup step is
charged; the final stack is exactly the canonical Boolean output. -/
theorem input_run (vars : List (List Bool)) (witness query : List Bool) :
    let bits := Shared.ComplexityBridge.TM2WitnessInput.inputBits
      (Shared.ComplexityBridge.TM2WitnessLookup.frames vars) witness query
    ∃ t ≤ timePolynomial.eval bits.length,
      runSteps machine.step t (Turing.initList machine bits) =
        some (Turing.haltList machine [Shared.ComplexityBridge.CNF.assignment
          (vars.map Computability.decodeNat) witness (Computability.decodeNat query)]) := by
  let first := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let inner := BitstringEncoding.bitEncode (witness,query)
  let bits := Shared.ComplexityBridge.TM2WitnessInput.inputBits first witness query
  let size := first.length+witness.length+query.length
  let answer := Shared.ComplexityBridge.CNF.assignment (vars.map Computability.decodeNat) witness (Computability.decodeNat query)
  let finish := Shared.ComplexityBridge.TM2WitnessInput.finalCfg first witness query
  let start := Shared.ComplexityBridge.TM2WitnessOutput.embed
    (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none first witness query [] [] [])
  obtain ⟨n,hn,hr⟩ := Shared.ComplexityBridge.TM2WitnessInput.load_input first witness query
  change n ≤ 4*bits.length+6 at hn
  change runSteps Load.step n (Turing.initList Load bits) = some finish at hr
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Load.step machine.step loadEmbed loadTerminal load_stable load_step n (Turing.initList Load bits) finish rfl hr
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2WitnessOutput.loaded_run_polynomial vars witness query
  change b ≤ Shared.ComplexityBridge.TM2WitnessOutput.timePolynomial.eval size at hb
  rw [Shared.ComplexityBridge.RawCNFLookup.lookup_correct] at hbr
  change runSteps Output.step b start = some (Turing.haltList Output [answer]) at hbr
  have hinner : inner.length = 6*witness.length+1+3*query.length := Shared.ComplexityBridge.bitstring_pair_encoded_length witness query
  have hbits : bits.length = 6*first.length+1+3*inner.length := Shared.ComplexityBridge.bitstring_pair_encoded_length first inner
  have hsize : size ≤ bits.length := by dsimp [size]; omega
  have hp := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono Shared.ComplexityBridge.TM2WitnessOutput.timePolynomial hsize
  have hb' : b ≤ Shared.ComplexityBridge.TM2WitnessOutput.timePolynomial.eval bits.length := le_trans hb hp
  have hbRun := out_run start b
  rw [hbr] at hbRun
  refine ⟨1+a+1+b,?_,?_⟩
  · change 1+a+1+b ≤ timePolynomial.eval bits.length
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  · change runSteps machine.step (1+a+1+b) (Turing.initList machine bits) = _
    rw [show 1+a+1+b = 1+(a+(1+b)) by omega,runSteps_add]
    change (machine.step (Turing.initList machine bits)).bind _ = _
    rw [startup]
    change runSteps machine.step (a+(1+b)) (loadEmbed (Turing.initList Load bits)) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+b) (loadEmbed finish) = _
    rw [runSteps_add]
    change (machine.step (loadEmbed finish)).bind _ = _
    rw [dispatch]
    change runSteps machine.step b (outEmbed start) = _
    rw [hbRun]
    change some (outEmbed (Turing.haltList Output [answer])) = some (Turing.haltList machine [answer])
    rw [out_halt]

namespace Fixtures
example : (runSteps machine.step 25 (Turing.initList machine
    (Shared.ComplexityBridge.TM2WitnessInput.inputBits [] [] []))).map
    (fun q => (q.l.isNone,q.stk .query)) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .query)) (runSteps machine.step 25
    (Turing.initList machine (Shared.ComplexityBridge.TM2WitnessInput.inputBits [] [] []))) : Option (Bool × List Bool)) = _
  decide
set_option maxRecDepth 4096 in
example : (runSteps machine.step 129 (Turing.initList machine
    (Shared.ComplexityBridge.TM2WitnessInput.inputBits
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]]) [true] [false,true]))).map
    (fun q => (q.l.isNone,q.stk .query)) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .query)) (runSteps machine.step 129
    (Turing.initList machine (Shared.ComplexityBridge.TM2WitnessInput.inputBits
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]]) [true] [false,true]))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2WitnessComplete
