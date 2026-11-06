import Shared.ComplexityBridge.TM2BooleanInput

/-! Primitive-recursive initialization from raw binary inputs and pairs.
This does not prove a bit-cost bound for the initializer or computability of
the numeric program decoder or interpreter. -/
namespace Shared.ComplexityBridge.TM2RawInput
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2Reification
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2Program

/-- Initialize directly from a raw binary input using the actual library
encoding as part of initialization. -/
def buildDecisionInput (p : InputRaw × List Bool) : Option ResultRaw :=
  buildRaw (p.1, BitstringEncoding.bitEncode p.2)

/-- Initialize directly from a raw input and binary witness. -/
def buildPairInput (p : InputRaw × (List Bool × List Bool)) : Option ResultRaw :=
  buildRaw (p.1, BitstringEncoding.bitEncode p.2)

theorem buildDecisionInput_primrec : Primrec buildDecisionInput := by
  exact buildRaw_primrec.comp (Primrec.pair Primrec.fst
    (Shared.Codes.VerifierPrograms.bitListEncoding_primrec.comp Primrec.snd))

theorem buildPairInput_primrec : Primrec buildPairInput := by
  exact buildRaw_primrec.comp (Primrec.pair Primrec.fst
    (Shared.Codes.VerifierPrograms.pairEncoding_primrec.comp Primrec.snd))

theorem buildDecisionInput_computable : Computable buildDecisionInput := buildDecisionInput_primrec.to_comp
theorem buildPairInput_computable : Computable buildPairInput := buildPairInput_primrec.to_comp

/-- The input lengths used by the actual initializer are the library's sizes. -/
theorem decisionEncoding_length (x : List Bool) :
    (BitstringEncoding.bitEncode x).length = 3 * x.length :=
  Shared.ComplexityBridge.bitstring_list_encoded_length x

theorem pairEncoding_length (x w : List Bool) :
    (BitstringEncoding.bitEncode (x, w)).length = 6 * x.length + 1 + 3 * w.length :=
  Shared.ComplexityBridge.bitstring_pair_encoded_length x w

/-- Canonical P coverage with the primitive-recursive initializer applied to
raw inputs and one fixed whole-block clock exponent. -/
theorem canonicalP_rawInput (L : ComplexityTheory.DecisionProblem)
    (hL : L ∈ ComplexityTheory.P) :
    ∃ (h : Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode (α := List Bool))
        (BitstringEncoding.bitEncode (α := Bool)) L)
      (N : Numbering h.tm.Γ h.tm.Λ h.tm.σ) (p : List Shared.Codes.TM2Statements.Code)
      (e : Nat) (d : InputRaw) (z o out k : Nat),
      decodeProgram e = some p ∧ validRaw d = true ∧
      programValid p N.stackCount N.states N.symbols = true ∧
      ∀ x, ∃ start r, buildDecisionInput (d, x) = some (resultRaw start) ∧
        run p ((x.length + 2) ^ k) start = .halted r ∧
        CfgRel N (Turing.haltList h.tm
          ((BitstringEncoding.bitEncode (L x)).map h.outputAlphabet.invFun)) (erase r) ∧
        Shared.ComplexityBridge.TM2BooleanOutput.extractMemory (z, o, out, r.label, r.memory) = some (L x) := by
  obtain ⟨h, N, p, e, d, z, o, out, k, he, hd, hv, hr⟩ := canonicalP_numericClock L hL
  have hvalid : validRaw (inputRaw d) = true := by
    change validInputData d = true
    exact hd
  refine ⟨h, N, p, e, inputRaw d, z, o, out, k, he, hvalid, hv, ?_⟩
  intro x
  obtain ⟨start, r, hs, hrun, hrel, hout⟩ := hr x
  exact ⟨start, r, hs, hrun, hrel, hout⟩

example : buildDecisionInput (inputRaw ⟨1, 1, 2, 1, 0, 0, 0, 0, 1⟩, []) =
    some (some 0, 0, [[]]) := by decide
example : buildDecisionInput (inputRaw ⟨1, 1, 2, 1, 0, 0, 0, 0, 1⟩, [true, false]) =
    some (some 0, 0, [[1, 1, 0, 1, 0, 0]]) := by decide
example : buildPairInput (inputRaw ⟨1, 1, 2, 1, 0, 0, 0, 0, 1⟩, ([], [])) =
    some (some 0, 0, [[0]]) := by decide
example : buildDecisionInput (inputRaw ⟨1, 1, 2, 1, 0, 0, 0, 0, 0⟩, []) = none := by decide

end Shared.ComplexityBridge.TM2RawInput
