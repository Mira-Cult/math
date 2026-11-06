import Shared.ComplexityBridge.TM2BitstringPoly
import Shared.ComplexityBridge.TM2BinaryFullTape

/-! The arbitrary-output evaluator reaches the full-tape finite binary
simulation. The fixed-width encoded tape boundaries remain explicit. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BitstringBinary
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2BitstringPoly
open Shared.ComplexityBridge.TM2BitstringOutput
open Shared.ComplexityBridge.TM2BinaryPostCosts

def whole (c : Shared.Codes.TM2Candidate.Candidate) (p : Shared.Codes.TM2Program.Program) : FinTM2 :=
  (wholeAux c p).tm

@[instance_reducible] def finiteAlphabet (c : Shared.Codes.TM2Candidate.Candidate) (p : Shared.Codes.TM2Program.Program)
    (k : (whole c p).K) : Fintype ((whole c p).Γ k) := by
  change Fintype (Shared.ComplexityBridge.TM2Combined.Alphabet
    (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw c.1.2.2).stackCount
    (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw c.1.2.2).symbols k)
  cases k with
  | inl b => exact inferInstanceAs (Fintype Bool)
  | inr i => exact inferInstance

/-- A fixed candidate and codec yield one finite table. Every successful
comparison reaches a binary encoding of a related representation of the
entire halted TM2 configuration, including its output stack, within a fixed
polynomial in the encoded input length. -/
theorem successful_full_tape (c : Shared.Codes.TM2Candidate.Candidate)
    (p : Shared.Codes.TM2Program.Program) (hdecode : decodeProgram c.1.1 = some p)
    {width : Nat} (enc : Alphabet (whole c p) → List.Vector Bool width)
    (dec : List.Vector Bool width → Alphabet (whole c p))
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) :
    let tm := whole c p
    let alphabet := finiteAlphabet c p
    let clock := timePolynomial
      (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw c.1.2.2).stackCount c.1.2.1 p
    let cost := 2*Shared.ComplexityBridge.TM2BinaryPostCosts.timePolynomial tm alphabet enc dec clock
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ program : Shared.Codes.FinitePrograms.Program, valid program = true ∧
      ∀ bits output, Evaluator.evaluate c bits = some output →
        ∃ d ≤ cost.eval bits.length, ∃ mid q t,
          TM2to1.TrCfg (Turing.haltList tm output) mid ∧
          run program (initial (inputBits tm enc bits)) d = some (.inr (q,t)) ∧
          Shared.ComplexityBridge.TM0FiniteProgram.tape t = TM1to1.trTape enc0 mid.Tape ∧
          step program (q,t) = some (.inl (TM1to1.trTape enc0 mid.Tape).head) := by
  let tm := whole c p
  let alphabet := finiteAlphabet c p
  let clock := timePolynomial
    (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw c.1.2.2).stackCount c.1.2.1 p
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨program,hvalid,hprogram⟩ :=
    Shared.ComplexityBridge.TM2BinaryFullTape.finite_program_full_tape tm alphabet enc dec enc0 encdec clock
  refine ⟨program,hvalid,?_⟩
  intro bits output heval
  obtain ⟨n,hn,hr⟩ := successful_whole_run c p hdecode bits output heval
  apply hprogram bits n (Turing.haltList tm output)
  · exact hr
  · exact hn
  · rfl

end Shared.ComplexityBridge.TM2BitstringBinary
