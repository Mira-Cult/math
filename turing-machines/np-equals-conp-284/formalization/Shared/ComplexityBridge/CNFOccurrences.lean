import Shared.ComplexityBridge.TM2TagInput
import Shared.ComplexityBridge.TM2FlattenBlocksCanonical

namespace Shared.ComplexityBridge.CNFOccurrences

/-- Extract raw variable names from the flattened outer block sequence. The
outer failure tag is preserved by routing it to a malformed stream. This
operation alone does not validate each original clause boundary. -/
def project (input : List Bool) : List Bool :=
  TM2LiteralStreamTotal.decodeResult (TM2TagInput.selectStream (TM2FlattenBlocksTotal.decodeResult input))

/-- All three finite machines and their canonical encoding adapters are charged. -/
theorem project_isPolyTime : ComplexityTheory.IsPolyTime project := by
  have hfirst := TM2Compose.isPolyTime_comp TM2FlattenBlocksTotal.decodeResult TM2TagInput.selectStream
    TM2FlattenBlocksCanonical.decodeResult_isPolyTime TM2TagInput.selectStream_isPolyTime
  have hsecond := TM2Compose.isPolyTime_comp
    (fun x => TM2TagInput.selectStream (TM2FlattenBlocksTotal.decodeResult x))
    TM2LiteralStreamTotal.decodeResult hfirst TM2LiteralStreamTotal.decodeResult_isPolyTime
  exact hsecond

/-- On every successfully parsed CNF, the output is the raw-name frame stream
whose decoded names are exactly the verifier's occurrence list. -/
theorem project_correct_of_parse (input : List Bool) (formula : CNF.Formula) (h : CNF.parse input = some formula) :
    ∃ names : List (List Bool),
      names.map Computability.decodeNat = CNF.variableOccurrences formula ∧
      project input = true::TM2WitnessLookup.frames names := by
  obtain ⟨literalStream,names,hflat,hvars,hstream⟩ := TM2LiteralStreamTotal.cnf_occurrences input formula h
  refine ⟨names,hvars,?_⟩
  simpa [project,hflat,TM2TagInput.selectStream] using hstream

/-- Malformed outer block framing is always rejected by the projection. -/
theorem project_outer_failure (input : List Bool) (h : BitstringEncoding.undelimitBlocks input = none) :
    project input = [false] := by
  simp only [project,TM2FlattenBlocksTotal.decodeResult,h,TM2FlattenBlocksTotal.encodeResult,TM2TagInput.selectStream]
  rw [TM2LiteralStreamTotal.decodeResult,TM2LiteralStream.parseNames_bad_frame true [] rfl]

namespace Fixtures
/-- The outer failure tag cannot be accidentally converted to success. -/
example : project [true] = [false] := project_outer_failure [true] rfl
/-- Original clause boundaries matter: these two malformed clauses concatenate
into one valid literal. The projection is not a complete CNF validator. -/
def crossedClauses : List Bool := TM2FlattenBlocks.framed [[true,false],[true,true,false]]
example : CNF.parse crossedClauses = none := by decide
example : project crossedClauses = [true,false] := by
  have hflat : TM2FlattenBlocksTotal.decodeResult crossedClauses =
      true::TM2WitnessLookup.frames [[false,true]] := by decide
  rw [project,hflat]
  change TM2LiteralStreamTotal.decodeResult (TM2WitnessLookup.frames [[false,true]]) = _
  rw [TM2LiteralStreamTotal.decodeResult,TM2LiteralStream.parseNames_framed]
  rfl
end Fixtures

end Shared.ComplexityBridge.CNFOccurrences
