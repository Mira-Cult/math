import Shared.ComplexityBridge.TM2FormulaOutput
import Shared.ComplexityBridge.TM2PreparedLoad
import Shared.ComplexityBridge.CNFPrepare

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2PreparedVerify
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Load := Shared.ComplexityBridge.TM2PreparedLoad.machine
abbrev Output := Shared.ComplexityBridge.TM2FormulaOutput.machine
abbrev LKey := Shared.ComplexityBridge.TM2WitnessLookup.Key
abbrev Key := Shared.ComplexityBridge.TM2FormulaOutput.Key
abbrev LoadLabel := Shared.ComplexityBridge.TM2PreparedLoad.Label
abbrev OutputLabel := Shared.ComplexityBridge.TM2FormulaOutput.Label
abbrev OutputState := Shared.ComplexityBridge.TM2FormulaOutput.State
abbrev Label := Unit ⊕ (LoadLabel ⊕ OutputLabel)
abbrev State := Option Bool ⊕ OutputState

def loadState : State → Option Bool | .inl v => v | _ => none
def outputState : State → OutputState | .inr v => v | _ => Output.initialState

def keyMap : LKey → Key
  | .vars => .inl (.inl (.inr .vars))
  | .witness => .inl (.inl (.inr .witness))
  | .query => .inr .stream
  | .scratch => .inr .scratch
  | .left => .inl (.inr .scratch)
  | .right => .inl (.inl (.inr .scratch))

def loadStacks (S : LKey → List Bool) (other : Key → List Bool) : Key → List Bool
  | .inr .stream => S .query
  | .inl (.inl (.inr .witness)) => S .witness
  | .inl (.inl (.inr .vars)) => S .vars
  | .inr .scratch => S .scratch
  | .inl (.inr .scratch) => S .left
  | .inl (.inl (.inr .scratch)) => S .right
  | k => other k
@[simp] theorem loadStacks_apply (S : LKey → List Bool) (other : Key → List Bool) (j : LKey) :
    loadStacks S other (keyMap j) = S j := by cases j <;> rfl

theorem load_update (S : LKey → List Bool) (other : Key → List Bool) (j : LKey) (xs : List Bool) :
    loadStacks (Function.update S j xs) other = Function.update (loadStacks S other) (keyMap j) xs := by
  funext k; cases j <;> cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => cases k <;> simp [loadStacks,keyMap,Function.update] <;> rfl
      | inr k => cases k <;> simp [loadStacks,keyMap,Function.update] <;> rfl
    | inr k => cases k <;> simp [loadStacks,keyMap,Function.update] <;> rfl
  | inr k => cases k <;> simp [loadStacks,keyMap,Function.update] <;> rfl

def loadEmbed (other : Key → List Bool) (q : Load.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),.inl q.var,loadStacks q.stk other⟩
def outEmbed (q : Output.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inr l)),.inr q.var,q.stk⟩

def liftLoad : Stmt (fun _ : LKey => Bool) LoadLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (keyMap j) (fun v => f (loadState v)) (liftLoad q)
  | .peek j f q => .peek (keyMap j) (fun v h => .inl (f (loadState v) h)) (liftLoad q)
  | .pop j f q => .pop (keyMap j) (fun v h => .inl (f (loadState v) h)) (liftLoad q)
  | .load f q => .load (fun v => .inl (f (loadState v))) (liftLoad q)
  | .branch f q r => .branch (fun v => f (loadState v)) (liftLoad q) (liftLoad r)
  | .goto f => .goto (fun v => .inr (.inl (f (loadState v))))
  | .halt => .halt

def liftOutput : Stmt (fun _ : Key => Bool) OutputLabel OutputState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push j (fun v => f (outputState v)) (liftOutput q)
  | .peek j f q => .peek j (fun v h => .inr (f (outputState v) h)) (liftOutput q)
  | .pop j f q => .pop j (fun v h => .inr (f (outputState v) h)) (liftOutput q)
  | .load f q => .load (fun v => .inr (f (outputState v))) (liftOutput q)
  | .branch f q r => .branch (fun v => f (outputState v)) (liftOutput q) (liftOutput r)
  | .goto f => .goto (fun v => .inr (.inr (f (outputState v))))
  | .halt => .halt

theorem liftLoad_aux (q : Load.Stmt) (v : Option Bool) (S : LKey → List Bool) (other : Key → List Bool) :
    stepAux (liftLoad q) (.inl v) (loadStacks S other) = loadEmbed other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => simp only [liftLoad,stepAux,loadState,loadStacks_apply]; rw [← load_update S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftLoad,stepAux,loadState,loadStacks_apply]; exact ih _ _
  | pop j f q ih => simp only [liftLoad,stepAux,loadState,loadStacks_apply]; rw [← load_update S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftLoad,stepAux,loadState,h,ihq,ihr]

theorem liftOutput_aux (q : Output.Stmt) (v : OutputState) (S : Key → List Bool) :
    stepAux (liftOutput q) (.inr v) S = outEmbed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftOutput,stepAux,outputState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl () => .load (fun _ => .inl none) (.goto (fun _ => .inr (.inl Load.main)))
  | .inr (.inl (.inr .ready)) => .load (fun _ => .inr Output.initialState) (.goto (fun _ => .inr (.inr Output.main)))
  | .inr (.inl l) => liftLoad (Shared.ComplexityBridge.TM2PreparedLoad.program l)
  | .inr (.inr l) => liftOutput (Shared.ComplexityBridge.TM2FormulaOutput.program l)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inl (.inl (.inr .vars))
  k₁ := .inr .stream
  Γ := fun _ => Bool
  Λ := Label
  main := .inl ()
  σ := State
  initialState := .inr Output.initialState
  m := program

def loadTerminal (q : Load.Cfg) : Prop := q.l = some (.inr .ready)
noncomputable instance : DecidablePred loadTerminal := fun _ => Classical.propDecidable _
theorem load_stable (q : Load.Cfg) (h : loadTerminal q) : Load.step q = some q := by
  cases q with
  | mk l v S => change l = some (.inr .ready) at h; subst l; rfl

theorem load_step (other : Key → List Bool) (q : Load.Cfg) (h : ¬ loadTerminal q) :
    machine.step (loadEmbed other q) = (Load.step q).map (loadEmbed other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inr p => cases p with
        | ready => exact False.elim (h rfl)
        | tag | clear =>
          change some (stepAux (liftLoad (Shared.ComplexityBridge.TM2PreparedLoad.program _)) (.inl v) (loadStacks S other)) = _
          rw [liftLoad_aux]; rfl
      | inl p =>
        change some (stepAux (liftLoad (Shared.ComplexityBridge.TM2PreparedLoad.program (.inl p))) (.inl v) (loadStacks S other)) = _
        rw [liftLoad_aux]; rfl

theorem out_step (q : Output.Cfg) : machine.step (outEmbed q) = (Output.step q).map outEmbed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftOutput (Shared.ComplexityBridge.TM2FormulaOutput.program l)) (.inr v) S) = _
      rw [liftOutput_aux]; rfl

theorem out_run (q : Output.Cfg) (n : Nat) :
    runSteps machine.step n (outEmbed q) = (runSteps Output.step n q).map outEmbed := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,out_step,runSteps_front]
    cases hs : Output.step q with
    | none => rfl
    | some next => exact ih next

theorem startup (bits : List Bool) :
    machine.step (Turing.initList machine bits) = some (loadEmbed (fun _ => []) (Turing.initList Load bits)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => cases k <;> simp [loadEmbed,loadStacks,Turing.initList,machine,Load,Shared.ComplexityBridge.TM2PreparedLoad.machine] <;> rfl
      | inr k => cases k <;> simp [loadEmbed,loadStacks,Turing.initList,machine,Load,Shared.ComplexityBridge.TM2PreparedLoad.machine] <;> rfl
    | inr k => cases k <;> simp [loadEmbed,loadStacks,Turing.initList,machine,Load,Shared.ComplexityBridge.TM2PreparedLoad.machine] <;> rfl
  | inr k => cases k <;> simp [loadEmbed,loadStacks,Turing.initList,machine,Load,Shared.ComplexityBridge.TM2PreparedLoad.machine] <;> rfl

theorem dispatch (frame witness input : List Bool) (v : Option Bool) :
    machine.step (loadEmbed (fun _ => []) (Shared.ComplexityBridge.TM2PreparedLoad.cfg .ready v frame witness input)) =
      some (outEmbed (Shared.ComplexityBridge.TM2FormulaOutput.embed
        (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none input frame witness))) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem out_halt (bits : List Bool) :
    outEmbed (Turing.haltList Output bits) = Turing.haltList machine bits := by
  rfl


noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 5*Polynomial.X+Polynomial.C 10+Shared.ComplexityBridge.TM2FormulaOutput.timePolynomial

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = 5*n+10+Shared.ComplexityBridge.TM2FormulaOutput.timePolynomial.eval n := by
  simp [timePolynomial]

theorem normalized_length_le (tag : List Bool) :
    (Shared.ComplexityBridge.TM2PreparedLoad.normalized tag).length ≤ tag.length := by
  cases tag with
  | nil => rfl
  | cons b tail => cases b <;> simp [Shared.ComplexityBridge.TM2PreparedLoad.normalized]

/-- Actual prepared-input machine: both parsing passes, normalization,
formula evaluation and halt cleanup are charged against the full encoding. -/
theorem run_for_frame (tag witness input : List Bool) (vars : List (List Bool))
    (hframe : Shared.ComplexityBridge.TM2PreparedLoad.normalized tag = Shared.ComplexityBridge.TM2WitnessLookup.frames vars) :
    let bits := Shared.ComplexityBridge.TM2PreparedLoad.inputBits tag witness input
    ∃ t ≤ timePolynomial.eval bits.length,
      runSteps machine.step t (Turing.initList machine bits) =
        some (Turing.haltList machine [(Shared.ComplexityBridge.RawCNFEval.formula vars witness input).getD false]) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let packed := BitstringEncoding.bitEncode (tag,input)
  let bits := Shared.ComplexityBridge.TM2PreparedLoad.inputBits tag witness input
  let size := frame.length+witness.length+input.length
  let start := Shared.ComplexityBridge.TM2FormulaOutput.embed
    (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none input frame witness)
  let answer := (Shared.ComplexityBridge.RawCNFEval.formula vars witness input).getD false
  obtain ⟨n,hn,v,hr⟩ := Shared.ComplexityBridge.TM2PreparedLoad.load_input tag witness input
  change n ≤ 5*bits.length+8 at hn
  change runSteps Load.step n (Turing.initList Load bits) = some (Shared.ComplexityBridge.TM2PreparedLoad.cfg .ready v (Shared.ComplexityBridge.TM2PreparedLoad.normalized tag) witness input) at hr
  rw [hframe] at hr
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Load.step machine.step (loadEmbed (fun _ => [])) loadTerminal load_stable (load_step (fun _ => []))
    n (Turing.initList Load bits) (Shared.ComplexityBridge.TM2PreparedLoad.cfg .ready v frame witness input) rfl hr
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2FormulaOutput.loaded_run vars witness input
  change b ≤ Shared.ComplexityBridge.TM2FormulaOutput.timePolynomial.eval size at hb
  change runSteps Output.step b start = some (Turing.haltList Output [answer]) at hbr
  have hpacked : packed.length = 6*tag.length+1+3*input.length := Shared.ComplexityBridge.bitstring_pair_encoded_length tag input
  have hbits : bits.length = 6*packed.length+1+3*witness.length := Shared.ComplexityBridge.bitstring_pair_encoded_length packed witness
  have hframeLen : frame.length ≤ tag.length := by
    change (Shared.ComplexityBridge.TM2WitnessLookup.frames vars).length ≤ tag.length
    rw [← hframe]
    exact normalized_length_le tag
  have hsize : size ≤ bits.length := by dsimp [size]; omega
  have hp := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono Shared.ComplexityBridge.TM2FormulaOutput.timePolynomial hsize
  have hb' : b ≤ Shared.ComplexityBridge.TM2FormulaOutput.timePolynomial.eval bits.length := le_trans hb hp
  have ho := out_run start b
  rw [hbr] at ho
  refine ⟨1+a+1+b,?_,?_⟩
  · rw [timePolynomial_eval]
    change 1+a+1+b ≤ 5*bits.length+10+Shared.ComplexityBridge.TM2FormulaOutput.timePolynomial.eval bits.length
    omega
  · change runSteps machine.step (1+a+1+b) (Turing.initList machine bits) = _
    rw [show 1+a+1+b = 1+(a+(1+b)) by omega,runSteps_add]
    change (machine.step (Turing.initList machine bits)).bind _ = _
    rw [startup]
    change runSteps machine.step (a+(1+b)) (loadEmbed (fun _ => []) (Turing.initList Load bits)) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+b) (loadEmbed (fun _ => []) (Shared.ComplexityBridge.TM2PreparedLoad.cfg .ready v frame witness input)) = _
    rw [runSteps_add]
    change (machine.step (loadEmbed (fun _ => []) (Shared.ComplexityBridge.TM2PreparedLoad.cfg .ready v frame witness input))).bind _ = _
    rw [dispatch]
    change runSteps machine.step b (outEmbed start) = _
    rw [ho]
    change some (outEmbed (Turing.haltList Output [answer])) = some (Turing.haltList machine [answer])
    rw [out_halt]

/-- Projection shape supplies a valid frame, and the resulting evaluation is
exactly the canonical certificate relation. Malformed formulas reject in both
projection branches, including flattened-projection false positives. -/
theorem projection_result (input witness : List Bool) :
    ∃ vars : List (List Bool),
      Shared.ComplexityBridge.TM2PreparedLoad.normalized (Shared.ComplexityBridge.CNFOccurrences.project input) =
        Shared.ComplexityBridge.TM2WitnessLookup.frames vars ∧
      (Shared.ComplexityBridge.RawCNFEval.formula vars witness input).getD false =
        Shared.ComplexityBridge.CNFWitness.verify (input,witness) := by
  cases hp : Shared.ComplexityBridge.CNF.parse input with
  | none =>
    rcases Shared.ComplexityBridge.CNFPrepare.project_shape input with hf | ⟨vars,hf⟩
    · refine ⟨[],?_,?_⟩
      · simp [hf,Shared.ComplexityBridge.TM2PreparedLoad.normalized,Shared.ComplexityBridge.TM2WitnessLookup.frames]
      · simp [Shared.ComplexityBridge.RawCNFEval.formula_eq,hp,Shared.ComplexityBridge.CNFWitness.verify]
    · refine ⟨vars,?_,?_⟩
      · simp [hf,Shared.ComplexityBridge.TM2PreparedLoad.normalized]
      · simp [Shared.ComplexityBridge.RawCNFEval.formula_eq,hp,Shared.ComplexityBridge.CNFWitness.verify]
  | some formula =>
    obtain ⟨vars,hvars,hproject⟩ := Shared.ComplexityBridge.CNFOccurrences.project_correct_of_parse input formula hp
    refine ⟨vars,?_,?_⟩
    · simp [hproject,Shared.ComplexityBridge.TM2PreparedLoad.normalized]
    · simp [Shared.ComplexityBridge.RawCNFEval.formula_eq,hp,hvars,Shared.ComplexityBridge.CNFWitness.verify]

def preparedEncoding (p : List Bool × List Bool) : List Bool :=
  BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFPrepare.prepare p)

theorem preparedEncoding_eq (input witness : List Bool) :
    preparedEncoding (input,witness) =
      Shared.ComplexityBridge.TM2PreparedLoad.inputBits (Shared.ComplexityBridge.CNFOccurrences.project input) witness input := rfl

/-- On every original input pair, the prepared encoding is consumed by the
finite verifier and the exact canonical Boolean result is output. -/
theorem prepared_run (input witness : List Bool) :
    ∃ t ≤ timePolynomial.eval (preparedEncoding (input,witness)).length,
      runSteps machine.step t (Turing.initList machine (preparedEncoding (input,witness))) =
        some (Turing.haltList machine [Shared.ComplexityBridge.CNFWitness.verify (input,witness)]) := by
  obtain ⟨vars,hframe,hanswer⟩ := projection_result input witness
  obtain ⟨t,ht,hr⟩ := run_for_frame (Shared.ComplexityBridge.CNFOccurrences.project input) witness input vars hframe
  refine ⟨t,?_,?_⟩
  · simpa [preparedEncoding_eq] using ht
  · simpa [preparedEncoding_eq,hanswer] using hr


/-- The finite verifier consumes the prepared encoding, with no preloaded
stacks and a polynomial bound in the complete prepared bitstring length. -/
noncomputable def preparedTimeMachine : Turing.TM2ComputableInPolyTime
    preparedEncoding (BitstringEncoding.bitEncode : Bool → List Bool)
    Shared.ComplexityBridge.CNFWitness.verify where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun p := by
    let t := Classical.choose (prepared_run p.1 p.2)
    have ht := (Classical.choose_spec (prepared_run p.1 p.2)).1
    have hr := (Classical.choose_spec (prepared_run p.1 p.2)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t] (some (Turing.initList machine ((preparedEncoding p).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFWitness.verify p)).map id))
      rw [List.map_id,List.map_id]
      change (fun o => o.bind machine.step)^[t] (some (Turing.initList machine (preparedEncoding p))) =
        some (Turing.haltList machine [Shared.ComplexityBridge.CNFWitness.verify p])
      simpa [t] using hr
    · simpa using ht

/-- Canonical polynomial time for the actual all-bitstrings SAT certificate
relation. The proof composes the finite preparation and verification machines,
including both encoding boundaries and intermediate-size costs. -/
theorem verify_isPolyTime : ComplexityTheory.IsPolyTime Shared.ComplexityBridge.CNFWitness.verify := by
  obtain ⟨hp⟩ := Shared.ComplexityBridge.CNFPrepare.prepare_isPolyTime
  let pre : Turing.TM2ComputableInPolyTime
      (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool) preparedEncoding id :=
    { toTM2ComputableAux := hp.toTM2ComputableAux
      time := hp.time
      outputsFun := hp.outputsFun }
  exact Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool) preparedEncoding
    (BitstringEncoding.bitEncode : Bool → List Bool) id Shared.ComplexityBridge.CNFWitness.verify
    pre preparedTimeMachine

/-- SAT membership in the pinned public NP class, with the proved linear
occurrence-witness bound and the concrete polynomial-time certificate relation. -/
theorem sat_in_NP : Shared.ComplexityBridge.CNF.sat ∈ ComplexityTheory.NP :=
  Shared.ComplexityBridge.CNFWitness.sat_in_NP_of_verifier_poly verify_isPolyTime


/-- SAT completeness now requires only the actual uniform many-one hardness
construction; membership is discharged by `sat_in_NP`. -/
noncomputable def complete_of_sat_hard (h : Shared.ComplexityBridge.CNFWitness.SatHard) :
    Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat :=
  Shared.ComplexityBridge.CNFWitness.complete_of_obligations verify_isPolyTime h

/-- Separate P = NP endpoint, conditional only on SAT hardness and the later
finite-machine comparison certificate. -/
theorem pnp_of_sat_hard {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M)
    (hhard : Shared.ComplexityBridge.CNFWitness.SatHard) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.ComplexityBridge.CNFWitness.pnp_conditional cert verify_isPolyTime hhard

/-- Separate NP = coNP endpoint, with its own comparison certificate and
the same explicitly stated, still-open SAT hardness obligation. -/
theorem npconp_of_sat_hard {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (hhard : Shared.ComplexityBridge.CNFWitness.SatHard) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.ComplexityBridge.CNFWitness.npconp_conditional cert verify_isPolyTime hhard


namespace Fixtures
/-- The crossed-clause false positive still produces false after the complete
prepared-input machine evaluates the original malformed formula. -/
example : ∃ t ≤ timePolynomial.eval
    (preparedEncoding (Shared.ComplexityBridge.CNFOccurrences.Fixtures.crossedClauses,[])).length,
    runSteps machine.step t (Turing.initList machine
      (preparedEncoding (Shared.ComplexityBridge.CNFOccurrences.Fixtures.crossedClauses,[]))) =
      some (Turing.haltList machine [false]) := by
  have hp := Shared.ComplexityBridge.CNFPrepare.malformed_can_project_success.1
  have hv := Shared.ComplexityBridge.CNFWitness.verify_malformed
    Shared.ComplexityBridge.CNFOccurrences.Fixtures.crossedClauses [] hp
  simpa [hv] using prepared_run Shared.ComplexityBridge.CNFOccurrences.Fixtures.crossedClauses []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
example : (runSteps machine.step 85 (Turing.initList machine
    (Shared.ComplexityBridge.TM2PreparedLoad.inputBits [true] [] []))).map
    (fun q => (q.l.isNone,q.stk (.inr .stream))) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr .stream)))
    (runSteps machine.step 85 (Turing.initList machine
      (Shared.ComplexityBridge.TM2PreparedLoad.inputBits [true] [] []))) : Option (Bool × List Bool)) = _
  decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
example : (runSteps machine.step 116 (Turing.initList machine
    (Shared.ComplexityBridge.TM2PreparedLoad.inputBits [true] [] [false]))).map
    (fun q => (q.l.isNone,q.stk (.inr .stream))) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr .stream)))
    (runSteps machine.step 116 (Turing.initList machine
      (Shared.ComplexityBridge.TM2PreparedLoad.inputBits [true] [] [false]))) : Option (Bool × List Bool)) = _
  decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
example : (runSteps machine.step 114 (Turing.initList machine
    (Shared.ComplexityBridge.TM2PreparedLoad.inputBits [false] [] [true]))).map
    (fun q => (q.l.isNone,q.stk (.inr .stream))) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr .stream)))
    (runSteps machine.step 114 (Turing.initList machine
      (Shared.ComplexityBridge.TM2PreparedLoad.inputBits [false] [] [true]))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2PreparedVerify
