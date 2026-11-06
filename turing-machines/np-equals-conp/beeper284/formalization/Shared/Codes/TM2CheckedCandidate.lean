import Shared.Codes.TM2Candidate
import Shared.Codes.TM2ValidationComputability
/-! A globally checked wrapper for the shared numeric TM2 candidate evaluator.
Every required table entry and both branches are validated before running a
candidate. Forward coverage of the canonical P class is retained. The
whole-block clock is not a bit-cost bound and the reverse model bridge remains
open. -/
namespace Shared.Codes.TM2CheckedCandidate
open Shared.Codes.TM2Candidate Shared.Codes.TM2Program Shared.Codes.TM2ValidationComputability
open Shared.Codes.TM2Micro Shared.Codes.TM2FixedComputability Shared.Codes.TM2StatementExecution
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2RawInput
open Shared.ComplexityBridge.TM2BooleanOutput

/-- Validate every statement against the finite bounds in the same candidate's
initialization parameters. -/
def candidateValid (c : Candidate) : Bool :=
  match decodeProgram c.1.1 with
  | none => false
  | some p => programValid p c.1.2.2.1.1 c.1.2.2.1.2.1 c.1.2.2.1.2.2

theorem candidateValid_primrec : Primrec candidateValid := by
  have hd : Primrec (fun c : Candidate => decodeProgram c.1.1) :=
    Shared.Codes.TM2Primcodable.decodeProgram_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec₂ (fun (c : Candidate) (p : Program) =>
      programValid p c.1.2.2.1.1 c.1.2.2.1.2.1 c.1.2.2.1.2.2) := by
    have hdata : Primrec (fun x : Candidate × Program => x.1.1.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have h := programValid_primrec.comp (Primrec.pair Primrec.snd hdata)
    apply h.to₂.of_eq
    intro c p
    rfl
  have h := Primrec.option_casesOn hd (Primrec.const false) hb
  apply h.of_eq
  intro c
  unfold candidateValid
  cases decodeProgram c.1.1 <;> rfl

def evaluate (c : Candidate) (input : List Bool) : Option Bool :=
  if candidateValid c then Shared.Codes.TM2Candidate.evaluate c input else none

theorem evaluate_primrec : Primrec₂ evaluate := by
  have hg : Primrec (fun x : Candidate × List Bool => candidateValid x.1) := candidateValid_primrec.comp Primrec.fst
  have he : Primrec (fun x : Candidate × List Bool => Shared.Codes.TM2Candidate.evaluate x.1 x.2) :=
    Shared.Codes.TM2Candidate.evaluate_primrec
  have h := Primrec.cond hg he (Primrec.const none)
  apply h.to₂.of_eq
  intro c input
  unfold evaluate
  cases candidateValid c <;> rfl

theorem evaluate_computable : Computable₂ evaluate := evaluate_primrec.to_comp

theorem invalid_rejected (c : Candidate) (input : List Bool) (h : candidateValid c = false) :
    evaluate c input = none := by simp [evaluate, h]

theorem invalid_program_rejected (c : Candidate) (input : List Bool) (p : Program)
    (hdecode : decodeProgram c.1.1 = some p)
    (hvalid : programValid p c.1.2.2.1.1 c.1.2.2.1.2.1 c.1.2.2.1.2.2 = false) :
    evaluate c input = none := by
  apply invalid_rejected
  simp [candidateValid, hdecode, hvalid]

/-- Every canonical P language has a globally validated, fixed-clock numeric
candidate. This is only the forward direction of a model bridge. -/
theorem canonicalP_covers (L : ComplexityTheory.DecisionProblem) (hL : L ∈ ComplexityTheory.P) :
    ∃ c : Candidate, candidateValid c = true ∧ ∀ x, evaluate c x = some (L x) := by
  obtain ⟨h,N,p,e,d,he,hd,hv,hr⟩ := canonicalPoly_boolean_io L hL
  obtain ⟨k,hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent h.time
  let z := outputSymbol h.toTM2ComputableAux N false
  let o := outputSymbol h.toTM2ComputableAux N true
  let out := (N.stack h.tm.k₁).val
  let c : Candidate := ((e,2*k,inputRaw d),(z,o,out))
  have hvalid : candidateValid c = true := by
    simp [candidateValid, c, he, inputRaw, hd, inputData, hv]
  refine ⟨c,hvalid,?_⟩
  intro x
  obtain ⟨start,r,hstart,hrun,hrel,hout⟩ := hr x
  have hinit : buildDecisionInput (inputRaw d,x) = some (resultRaw start) := by
    simp [buildDecisionInput, buildRaw_eq, hstart]
  have hclock : h.time.eval (BitstringEncoding.bitEncode x).length ≤ (x.length+2)^(2*k) := by
    apply le_trans (hk _)
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length]
    exact threeLength_clock_bound x.length k
  have hrun' : run p ((x.length+2)^(2*k)) start = .halted r := run_halted_mono p start r hclock hrun
  have heval : runEncoded ((e,(x.length+2)^(2*k)),resultRaw start) = some (true,resultRaw r) := by
    simpa [hrun', outcomeRaw] using runEncoded_of_decode e p ((x.length+2)^(2*k)) start he
  unfold evaluate
  rw [hvalid]
  simp only [↓reduceIte]
  change (buildDecisionInput (inputRaw d,x)).bind (fun start' =>
    (runEncoded ((e,(x.length+2)^(2*k)),start')).bind fun (v : Bool × ResultRaw) =>
      if v.1 then extractMemory (z,o,out,v.2.1,v.2.2.2) else none) = some (L x)
  rw [hinit]
  change (runEncoded ((e,(x.length+2)^(2*k)),resultRaw start)).bind _ = some (L x)
  rw [heval]
  simpa [resultRaw, z, o, out] using hout

example : candidateValid
    ((Encodable.encode ([.branch [0] .halt (.goto [])] : Program),0,
      ((1,1,2),(1,0,0),(0,0,1))),(0,1,0)) = false := by
  simp [candidateValid, decodeProgram, programValid, Shared.Codes.TM2StatementValidation.valid,
    Shared.Codes.TM2StatementValidation.unaryValid, Shared.Codes.FiniteTables.lookup]

example : evaluate
    ((Encodable.encode ([.branch [0] .halt (.goto [])] : Program),0,
      ((1,1,2),(1,0,0),(0,0,1))),(0,1,0)) [] = none := by
  apply invalid_rejected
  simp [candidateValid, decodeProgram, programValid, Shared.Codes.TM2StatementValidation.valid,
    Shared.Codes.TM2StatementValidation.unaryValid, Shared.Codes.FiniteTables.lookup]

end Shared.Codes.TM2CheckedCandidate
