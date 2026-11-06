import Shared.Beeping.NPcoNP.Source284CompileRecordsTM2
import Shared.Beeping.NPcoNP.Source284CompileRecordsBounds
import Shared.Beeping.NPcoNP.Source284TableRowsTM2
import Shared.Beeping.NPcoNP.Source284FiniteProgramRun

/-! Uniform compilation of a finite binary program to the 284 source's
unary-record bit representation. Polynomial time holds for all inputs;
validity is needed only for the semantic statements, because oversized
records of invalid programs may be clipped by the bounded serializer.
The resulting source has no loaded witness and this file does not prove
SAT hardness or a reduction involving certificate loading. -/
namespace Shared.Beeping.NPcoNP.Source284CompileBitsTM2

open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284CompileRecords
open Shared.Beeping.NPcoNP.Source284CompileRecordsBounds
open Shared.Beeping.NPcoNP.Source284CompileRecordsTM2
open Shared.Beeping.NPcoNP.Source284TableRowsTM2
open Shared.ComplexityBridge

/-- An explicit finite program's source records, serialized as bits. -/
def compileBits (p : Program) : List Bool := serializeRows (records p)

/-- Binary input and output use the canonical `BitstringEncoding` and all
numeric operations are provided by the proved TM2 constructions. -/
theorem compileBits_isPolyTime : ComplexityTheory.IsPolyTime compileBits :=
  TM2Compose.isPolyTime_comp records serializeRows records_isPolyTime serializeRows_isPolyTime

/-- Zero-tail serialization agrees on bounded acceptance with the original
sentinel-tail encoding for every valid finite program, input and certificate. -/
theorem compileBits_accepts (p : Program) (hv : valid p = true)
    (input certificate clock : Nat) :
    Source284Relative.accepts (value (compileBits p)) input certificate clock =
      Source284Relative.accepts (compile p) input certificate clock := by
  simpa only [compileBits, compile] using
    serializeRows_sentinel_accepts (records p) (records_fit_budget p hv)
      input certificate clock

/-- An initial finite-program tape and its compiled source agree on bounded
acceptance at the same clock, with source certificate fixed to zero. The list
is interpreted as blank-extended tape contents, not a length-delimited string;
the clock here does not charge compilation or witness loading. -/
theorem bounded_acceptance (p : Program) (hv : valid p = true)
    (input : List Bool) (clock : Nat) :
    Source284Relative.accepts (value (compileBits p)) (value input) 0 clock = true ↔
      bounded p input clock = some true := by
  rw [compileBits_accepts p hv]
  exact Source284FiniteProgramRun.bounded_acceptance_shared p input clock hv

end Shared.Beeping.NPcoNP.Source284CompileBitsTM2
