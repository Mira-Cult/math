import Shared.ComplexityBridge.TM2FiniteReverse

namespace Shared.ComplexityBridge.TM2FiniteBoundary
open Shared.ComplexityBridge.TM2FiniteReverse Shared.ComplexityBridge.TM2BooleanInput
open Shared.ComplexityBridge.TM2BooleanOutput Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation Shared.Codes.TM2Program
open Shared.Codes.TM2Micro Shared.Codes.TM2FixedComputability

/-- A successfully initialized input is a valid numeric configuration when
its main label is also in the actual decoded program. -/
theorem buildStart_valid (d : InputData) (bits : List Bool) (p : Program)
    (hdata : validInputData d = true) (hmain : d.main < p.length) :
    ∃ start, buildStart d bits = some start ∧
      resultValid d.stackCount d.states d.symbols p.length start := by
  have hd := hdata
  simp only [validInputData, Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨⟨⟨⟨⟨hl,hs⟩,hi⟩,hz⟩,ho⟩,hne⟩ := hd
  let mem := (List.replicate d.stackCount []).set d.inputStack
    (bits.map (inputBit d.falseSymbol d.trueSymbol))
  let start : Result := ⟨some d.main, d.initialState, mem⟩
  refine ⟨start, ?_, ?_⟩
  · simp [buildStart, hdata, start, mem]
  · refine ⟨hs, ?_, ?_⟩
    · apply valid_set
      · constructor
        · simp
        · intro stk hstk x hx
          have : stk = [] := by simpa using (List.eq_of_mem_replicate hstk)
          simp [this] at hx
      · intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        cases b
        · simpa [inputBit] using hz
        · simpa [inputBit] using ho
    · intro l hlab
      have : l = d.main := by simpa [start] using hlab.symm
      simpa [this] using hmain

/-- A successful Boolean output must name a real stack. An out-of-range
lookup is empty and cannot be mistaken for a Boolean output. -/
theorem extract_stack_in_range {ks symbols z o out : Nat} (r : Result)
    (hr : stacksValid ks symbols r.memory) (b : Bool)
    (he : extractMemory (z,o,out,r.label,r.memory) = some b) : out < ks := by
  by_contra h
  have hn : r.memory[out]? = none := by
    apply List.getElem?_eq_none
    have hlen := hr.1
    omega
  have hs : stackFn r.memory out = [] := by simp [stackFn, hn]
  cases hl : r.label <;> simp [extractMemory, extractOutput, decodeStack, hs, hl] at he

/-- Numeric Boolean extraction agrees with the related finite machine's
actual output stack. This does not claim any cleanup of other stacks. -/
theorem extract_from_related {ks states symbols labels z o out : Nat}
    (r : Result) (c : Turing.TM2.Cfg (fun _ : Fin (ks+1) => Fin (symbols+1))
      (Fin (labels+1)) (Fin (states+1)))
    (hr : resultValid ks states symbols labels r)
    (hrel : CfgRel ks states symbols labels c (erase r)) (b : Bool)
    (he : extractMemory (z,o,out,r.label,r.memory) = some b) :
    c.l = none ∧ decodeStack (z,o,(c.stk (clip ks out)).map Fin.val) = some b := by
  have hout : out < ks := extract_stack_in_range r hr.2.1 b he
  have hidx : (clip ks out).val = out := clip_val ks out (by omega)
  have hstack := hrel.2.2 (clip ks out)
  rw [hidx] at hstack
  change stackFn r.memory out = (c.stk (clip ks out)).map Fin.val at hstack
  have hl : r.label = none := by
    cases hx : r.label with
    | none => rfl
    | some l => simp [extractMemory, extractOutput, hx] at he
  have hc : c.l = none := by
    have h := hrel.1
    change r.label = c.l.map Fin.val at h
    rw [hl] at h
    cases hx : c.l <;> simp [hx, Option.map] at h ⊢
  refine ⟨hc, ?_⟩
  rw [← hstack]
  simpa [extractMemory, extractOutput, hl] using he

/-- A successful checked numeric execution is witnessed by a terminating
finite-core run with the same decoded output, using whole-block timing. -/
theorem finite_run_output (ks states symbols : Nat) (p : Program)
    (inputStack outputStack initialLabel initialState fuel z o out : Nat)
    (hp : programValid p ks states symbols = true)
    (d r : Result) (hd : resultValid ks states symbols p.length d)
    (hrun : run p fuel d = .halted r) (b : Bool)
    (he : extractMemory (z,o,out,r.label,r.memory) = some b) :
    ∃ n ≤ fuel, ∃ c',
      runSteps (finiteCore ks states symbols p inputStack outputStack initialLabel initialState).step n
        (finiteConfig ks states symbols p.length d) = some c' ∧
      c'.l = none ∧ decodeStack (z,o,(c'.stk (clip ks out)).map Fin.val) = some b := by
  have hs : resultValid ks states symbols p.length r := by
    have h := run_safe p ks states symbols hp fuel d hd
    rw [hrun] at h
    exact h.1
  have h := finite_run_from_config ks states symbols p inputStack outputStack initialLabel initialState hp fuel d hd
  rw [hrun] at h
  obtain ⟨n, hn, c', hsteps, hrel, hhalt⟩ := h
  exact ⟨n, hn, c', hsteps, (extract_from_related r c' hs hrel b he).1,
    (extract_from_related r c' hs hrel b he).2⟩

/-- For either a decision input or a witness pair, any library-encoded bit
sequence can be loaded into a valid numeric start and simulated by the finite
core. This describes the encoded start, not yet a TM2 loading program. -/
theorem finite_run_from_encoded_input (d : InputData) (bits : List Bool) (p : Program)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (fuel : Nat)
    (outputStack : Nat) :
    ∃ start, buildRaw (inputRaw d,bits) = some (resultRaw start) ∧
      finiteOutcome d.stackCount d.states d.symbols p d.inputStack outputStack d.main d.initialState fuel
        (finiteConfig d.stackCount d.states d.symbols p.length start) (run p fuel start) := by
  obtain ⟨start,hstart,hvalid⟩ := buildStart_valid d bits p hdata hmain
  refine ⟨start, ?_, ?_⟩
  · rw [buildRaw_eq, hstart]
    rfl
  · exact finite_run_from_config d.stackCount d.states d.symbols p d.inputStack outputStack d.main d.initialState hp fuel start hvalid

/-- Specialization to the pinned library encoding of raw decision inputs. -/
theorem finite_run_from_decision_input (d : InputData) (x : List Bool) (p : Program)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (fuel : Nat)
    (outputStack : Nat) :
    ∃ start, Shared.ComplexityBridge.TM2RawInput.buildDecisionInput (inputRaw d,x) = some (resultRaw start) ∧
      finiteOutcome d.stackCount d.states d.symbols p d.inputStack outputStack d.main d.initialState fuel
        (finiteConfig d.stackCount d.states d.symbols p.length start) (run p fuel start) := by
  exact finite_run_from_encoded_input d (BitstringEncoding.bitEncode x) p hdata hmain hp fuel outputStack

/-- The corresponding pair input uses the pinned pair encoding unchanged. -/
theorem finite_run_from_pair_input (d : InputData) (x w : List Bool) (p : Program)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (fuel : Nat)
    (outputStack : Nat) :
    ∃ start, Shared.ComplexityBridge.TM2RawInput.buildPairInput (inputRaw d,(x,w)) = some (resultRaw start) ∧
      finiteOutcome d.stackCount d.states d.symbols p d.inputStack outputStack d.main d.initialState fuel
        (finiteConfig d.stackCount d.states d.symbols p.length start) (run p fuel start) := by
  exact finite_run_from_encoded_input d (BitstringEncoding.bitEncode (x,w)) p hdata hmain hp fuel outputStack

/-- For a validated candidate whose main label is in its program, every
successful checked decision evaluation has a matching finite-core run with the
same Boolean output. This starts after input loading and does not clean up. -/
theorem checked_evaluate_finite_run (d : InputData) (p : Program) (e k z o out : Nat)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hdecode : decodeProgram e = some p)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b) :
    ∃ start n, buildStart d (BitstringEncoding.bitEncode x) = some start ∧
      n ≤ (x.length+2)^k ∧ ∃ c',
      runSteps (finiteCore d.stackCount d.states d.symbols p d.inputStack out d.main d.initialState).step n
        (finiteConfig d.stackCount d.states d.symbols p.length start) = some c' ∧
      c'.l = none ∧ decodeStack (z,o,(c'.stk (clip d.stackCount out)).map Fin.val) = some b := by
  obtain ⟨start,hstart,hvalid⟩ := buildStart_valid d (BitstringEncoding.bitEncode x) p hdata hmain
  have hin : Shared.ComplexityBridge.TM2RawInput.buildDecisionInput (inputRaw d,x) = some (resultRaw start) := by
    change buildRaw (inputRaw d,BitstringEncoding.bitEncode x) = _
    rw [buildRaw_eq, hstart]
    rfl
  have hval : Shared.Codes.TM2CheckedCandidate.candidateValid ((e,k,inputRaw d),(z,o,out)) = true := by
    simpa [Shared.Codes.TM2CheckedCandidate.candidateValid, hdecode, inputRaw] using hp
  have heval' : Shared.Codes.TM2Candidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b := by
    simpa [Shared.Codes.TM2CheckedCandidate.evaluate, hval] using heval
  have hrun := runEncoded_of_decode e p ((x.length+2)^k) start hdecode
  unfold Shared.Codes.TM2Candidate.evaluate at heval'
  rw [hin] at heval'
  change (runEncoded ((e,(x.length+2)^k), resultRaw start)).bind (fun v =>
    if v.1 then extractMemory (z,o,out,v.2.1,v.2.2.2) else none) = some b at heval'
  rw [hrun] at heval'
  cases hout : run p ((x.length+2)^k) start with
  | invalid => simp [hout, outcomeRaw] at heval'
  | timeout r => simp [hout, outcomeRaw] at heval'
  | halted r =>
    have he : extractMemory (z,o,out,r.label,r.memory) = some b := by
      simpa [hout, outcomeRaw, resultRaw] using heval'
    obtain ⟨n,hn,c',hs,hl,hout'⟩ := finite_run_output d.stackCount d.states d.symbols p
      d.inputStack out d.main d.initialState ((x.length+2)^k) z o out hp start r hvalid hout b he
    exact ⟨start,n,hstart,hn,c',hs,hl,hout'⟩

/-- A successful evaluation cannot start outside the actual program table,
even when the input descriptor claims a larger label universe. -/
theorem checked_evaluate_main_in_range (d : InputData) (p : Program) (e k z o out : Nat)
    (hdata : validInputData d = true) (hdecode : decodeProgram e = some p)
    (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b) :
    d.main < p.length := by
  by_contra hmain
  have hn : p[d.main]? = none := by
    apply List.getElem?_eq_none
    omega
  let start : Result := ⟨some d.main, d.initialState,
    (List.replicate d.stackCount []).set d.inputStack
      ((BitstringEncoding.bitEncode x).map (inputBit d.falseSymbol d.trueSymbol))⟩
  have hstart : buildStart d (BitstringEncoding.bitEncode x) = some start := by
    simp [buildStart, hdata, start]
  have hin : Shared.ComplexityBridge.TM2RawInput.buildDecisionInput (inputRaw d,x) = some (resultRaw start) := by
    change buildRaw (inputRaw d,BitstringEncoding.bitEncode x) = _
    rw [buildRaw_eq, hstart]
    rfl
  have heval' : Shared.Codes.TM2Candidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b := by
    unfold Shared.Codes.TM2CheckedCandidate.evaluate at heval
    split at heval
    · exact heval
    · contradiction
  have hrun := runEncoded_of_decode e p ((x.length+2)^k) start hdecode
  unfold Shared.Codes.TM2Candidate.evaluate at heval'
  rw [hin] at heval'
  change (runEncoded ((e,(x.length+2)^k), resultRaw start)).bind (fun v =>
    if v.1 then extractMemory (z,o,out,v.2.1,v.2.2.2) else none) = some b at heval'
  rw [hrun] at heval'
  cases hf : (x.length+2)^k with
  | zero => simp [hf, run, start, outcomeRaw] at heval'
  | succ n => simp [hf, run, start, hn, outcomeRaw] at heval'

/-- Main-label validity follows from successful evaluation, so callers do not
need to impose that additional check on the candidate representation. -/
theorem checked_evaluate_finite_run' (d : InputData) (p : Program) (e k z o out : Nat)
    (hdata : validInputData d = true) (hdecode : decodeProgram e = some p)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b) :
    ∃ start n, buildStart d (BitstringEncoding.bitEncode x) = some start ∧
      n ≤ (x.length+2)^k ∧ ∃ c',
      runSteps (finiteCore d.stackCount d.states d.symbols p d.inputStack out d.main d.initialState).step n
        (finiteConfig d.stackCount d.states d.symbols p.length start) = some c' ∧
      c'.l = none ∧ decodeStack (z,o,(c'.stk (clip d.stackCount out)).map Fin.val) = some b :=
  checked_evaluate_finite_run d p e k z o out hdata
    (checked_evaluate_main_in_range d p e k z o out hdata hdecode x b heval)
    hdecode hp x b heval

/-- A successful comparison necessarily passed both candidate and input
validation and decoded a globally valid program. -/
theorem checked_evaluate_validation (d : InputData) (e k z o out : Nat) (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b) :
    validInputData d = true ∧ ∃ p, decodeProgram e = some p ∧
      programValid p d.stackCount d.states d.symbols = true := by
  have hcandidate : Shared.Codes.TM2CheckedCandidate.candidateValid ((e,k,inputRaw d),(z,o,out)) = true := by
    cases hv : Shared.Codes.TM2CheckedCandidate.candidateValid ((e,k,inputRaw d),(z,o,out)) with
    | false => simp [Shared.Codes.TM2CheckedCandidate.evaluate, hv] at heval
    | true => rfl
  have hinput : validInputData d = true := by
    cases hd : validInputData d with
    | true => rfl
    | false =>
      have heval' : Shared.Codes.TM2Candidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b := by
        simpa [Shared.Codes.TM2CheckedCandidate.evaluate, hcandidate] using heval
      have hin : Shared.ComplexityBridge.TM2RawInput.buildDecisionInput (inputRaw d,x) = none := by
        change buildRaw (inputRaw d,BitstringEncoding.bitEncode x) = none
        rw [buildRaw_eq]
        simp [buildStart, hd]
      unfold Shared.Codes.TM2Candidate.evaluate at heval'
      rw [hin] at heval'
      contradiction
  refine ⟨hinput, ?_⟩
  cases hd : decodeProgram e with
  | none => simp [Shared.Codes.TM2CheckedCandidate.candidateValid, hd] at hcandidate
  | some p =>
    refine ⟨p,rfl,?_⟩
    simpa [Shared.Codes.TM2CheckedCandidate.candidateValid, hd, inputRaw] using hcandidate

/-- Every successful checked decision candidate has a related finite TM2 run
and a matching output, without separate input or program validation hypotheses. -/
theorem checked_evaluate_finite_run_complete (d : InputData) (e k z o out : Nat) (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate ((e,k,inputRaw d),(z,o,out)) x = some b) :
    ∃ p start n, decodeProgram e = some p ∧
      buildStart d (BitstringEncoding.bitEncode x) = some start ∧
      n ≤ (x.length+2)^k ∧ ∃ c',
      runSteps (finiteCore d.stackCount d.states d.symbols p d.inputStack out d.main d.initialState).step n
        (finiteConfig d.stackCount d.states d.symbols p.length start) = some c' ∧
      c'.l = none ∧ decodeStack (z,o,(c'.stk (clip d.stackCount out)).map Fin.val) = some b := by
  obtain ⟨hdata,p,hdecode,hp⟩ := checked_evaluate_validation d e k z o out x b heval
  obtain ⟨start,n,hstart,hn,c',hs,hl,hout⟩ := checked_evaluate_finite_run' d p e k z o out hdata hdecode hp x b heval
  exact ⟨p,start,n,hdecode,hstart,hn,c',hs,hl,hout⟩

/-- The structured view of a raw input descriptor loses no fields. -/
def inputDataOfRaw (r : InputRaw) : InputData :=
  ⟨r.1.1, r.1.2.1, r.1.2.2, r.2.1.1, r.2.1.2.1, r.2.1.2.2,
    r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩

@[simp] theorem inputRaw_ofRaw (r : InputRaw) : inputRaw (inputDataOfRaw r) = r := by
  rcases r with ⟨⟨ks,st,sy⟩,⟨la,ma,ini⟩,⟨input,z,o⟩⟩
  rfl

/-- Uniform version for the entire existing candidate representation. -/
theorem checked_evaluate_any_finite_run (c : Shared.Codes.TM2Candidate.Candidate)
    (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate c x = some b) :
    let d := inputDataOfRaw c.1.2.2
    ∃ p start n, decodeProgram c.1.1 = some p ∧
      buildStart d (BitstringEncoding.bitEncode x) = some start ∧
      n ≤ (x.length+2)^c.1.2.1 ∧ ∃ c',
      runSteps (finiteCore d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState).step n
        (finiteConfig d.stackCount d.states d.symbols p.length start) = some c' ∧
      c'.l = none ∧ decodeStack (c.2.1,c.2.2.1,(c'.stk (clip d.stackCount c.2.2.2)).map Fin.val) = some b := by
  have h := checked_evaluate_finite_run_complete (inputDataOfRaw c.1.2.2) c.1.1 c.1.2.1 c.2.1 c.2.2.1 c.2.2.2 x b
  have he : Shared.Codes.TM2CheckedCandidate.evaluate
      ((c.1.1,c.1.2.1,inputRaw (inputDataOfRaw c.1.2.2)),(c.2.1,c.2.2.1,c.2.2.2)) x = some b := by
    simpa using heval
  exact h he

/-- The declared label bound can exceed the program, but an out-of-table
main label cannot produce a successful result. -/
example : Shared.Codes.TM2CheckedCandidate.evaluate
    ((Encodable.encode ([.halt] : Program),0,
      inputRaw ⟨1,1,2,5,4,0,0,0,1⟩),(0,1,0)) [] = none := by
  cases h : Shared.Codes.TM2CheckedCandidate.evaluate
      ((Encodable.encode ([.halt] : Program),0,
        inputRaw ⟨1,1,2,5,4,0,0,0,1⟩),(0,1,0)) [] with
  | none => rfl
  | some b =>
    have hlt := checked_evaluate_main_in_range ⟨1,1,2,5,4,0,0,0,1⟩ [.halt]
      (Encodable.encode ([.halt] : Program)) 0 0 1 0 (by decide)
      (decodeProgram_coverage [.halt]) [] b h
    simp at hlt

end Shared.ComplexityBridge.TM2FiniteBoundary
