import Shared.ComplexityBridge.TM2Diagonal
import Shared.ComplexityBridge.CNFOccurrences

namespace Shared.ComplexityBridge.CNFPrepare

/-- Pack the tagged occurrence projection alongside the unchanged input. -/
def packed (input : List Bool) : List Bool :=
  BitstringEncoding.bitEncode (CNFOccurrences.project input,input)

/-- The witness is preserved exactly, including zero-length witnesses. -/
def prepare (p : List Bool × List Bool) : List Bool × List Bool :=
  (packed p.1,p.2)

theorem packed_isPolyTime : ComplexityTheory.IsPolyTime packed :=
  TM2Diagonal.packed_with_input_isPolyTime CNFOccurrences.project CNFOccurrences.project_isPolyTime

theorem prepare_isPolyTime : ComplexityTheory.IsPolyTime prepare :=
  TM2PairMap.pairMap_isPolyTime packed packed_isPolyTime

/-- The bytes encode precisely the projection and the original formula bits. -/
theorem packed_decode (input : List Bool) :
    (BitstringEncoding.bitDecode (packed input) : Option (List Bool × List Bool)) =
      some (CNFOccurrences.project input,input) :=
  BitstringEncoding.bitDecode_bitEncode _

/-- Projection has either its explicit failure tag or a valid list of framed
raw names, even for inputs that are not valid formulas. -/
theorem project_shape (input : List Bool) :
    CNFOccurrences.project input = [false] ∨
      ∃ vars : List (List Bool), CNFOccurrences.project input = true::TM2WitnessLookup.frames vars := by
  unfold CNFOccurrences.project TM2LiteralStreamTotal.decodeResult
  cases h : TM2LiteralStream.parseNames (TM2TagInput.selectStream (TM2FlattenBlocksTotal.decodeResult input)) with
  | none => left; rfl
  | some vars => right; exact ⟨vars,rfl⟩

/-- On a valid formula, the retained occurrence names denote exactly the
canonical verifier's variables and the original formula remains unchanged. -/
theorem prepare_valid (input witness : List Bool) (formula : CNF.Formula) (h : CNF.parse input = some formula) :
    ∃ vars : List (List Bool),
      vars.map Computability.decodeNat = CNF.variableOccurrences formula ∧
      (BitstringEncoding.bitDecode (prepare (input,witness)).1 : Option (List Bool × List Bool)) =
        some (true::TM2WitnessLookup.frames vars,input) ∧
      (prepare (input,witness)).2 = witness := by
  obtain ⟨vars,hvars,hproject⟩ := CNFOccurrences.project_correct_of_parse input formula h
  refine ⟨vars,hvars,?_,rfl⟩
  simpa [prepare,hproject] using packed_decode input

/-- A malformed formula may have a successful flattened projection, so the
retained formula must still be validated by the downstream evaluator. -/
theorem malformed_can_project_success :
    CNF.parse CNFOccurrences.Fixtures.crossedClauses = none ∧
      CNFOccurrences.project CNFOccurrences.Fixtures.crossedClauses = [true,false] := by
  constructor
  · decide
  · have hflat : TM2FlattenBlocksTotal.decodeResult CNFOccurrences.Fixtures.crossedClauses =
        true::TM2WitnessLookup.frames [[false,true]] := by decide
    rw [CNFOccurrences.project,hflat]
    change TM2LiteralStreamTotal.decodeResult (TM2WitnessLookup.frames [[false,true]]) = _
    rw [TM2LiteralStreamTotal.decodeResult,TM2LiteralStream.parseNames_framed]
    rfl

end Shared.ComplexityBridge.CNFPrepare
