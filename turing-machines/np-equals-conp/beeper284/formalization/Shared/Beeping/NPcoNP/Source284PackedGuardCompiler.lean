import Shared.Beeping.NPcoNP.Source284ParsedPolynomialGuard
import Shared.Beeping.NPcoNP.Source284FiniteProgramRun
import Shared.ComplexityBridge.FiniteVerifierCompiler
import Shared.Codes.FiniteProgramRepair
import Shared.Beeping.NPcoNP.Source284ConstantEncodedRowsTM2

/-! A single finite program for the parsed polynomial guard checker, on an
already canonical-encoded pair of input and certificate bit lists. The
compiler is existential, as permitted for abstract TM2 witnesses. No loader
from the 284 machine's original two tape halves is constructed here. -/
namespace Shared.Beeping.NPcoNP.Source284PackedGuardCompiler

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Codes.BitNumeralCompare (value)

def relation (p time : Polynomial Nat) (original : EncRows) (x : List Bool × List Bool) : Bool :=
  Source284ParsedPolynomialGuard.check p time (original,x)

theorem relation_isPolyTime (p time : Polynomial Nat) (original : EncRows) :
    IsPolyTime (relation p time original) := by
  let fixed : (List Bool × List Bool) → EncRows := fun _ => original
  have hf : IsPolyTime fixed := Source284ConstantEncodedRowsTM2.constRows_isPolyTime original
  have hi : IsPolyTime (id : (List Bool × List Bool) → (List Bool × List Bool)) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ha := TM2GuardAllStep.pair_isPolyTime fixed id hf hi
  exact TM2Compose.isPolyTime_comp (fun x : List Bool × List Bool => (fixed x,x))
    (Source284ParsedPolynomialGuard.check p time) ha
    (Source284ParsedPolynomialGuard.check_isPolyTime p time)

/-- One valid finite binary table computes the whole checker for every pair;
its program and polynomial are chosen once and do not vary with the input. -/
theorem finite_program (p time : Polynomial Nat) (original : EncRows) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧ ∀ input certificate,
      bounded program (BitstringEncoding.bitEncode (input,certificate))
        (clock.eval (BitstringEncoding.bitEncode (input,certificate)).length) =
          some (relation p time original (input,certificate)) := by
  obtain ⟨program,clock,hcorrect⟩ :=
    FiniteVerifierCompiler.canonical_finite_verifier_compiler (relation p time original)
      (relation_isPolyTime p time original)
  refine ⟨Shared.Codes.FiniteProgramRepair.repair program,clock,
    Shared.Codes.FiniteProgramRepair.repair_valid program,?_⟩
  intro input certificate
  rw [Shared.Codes.FiniteProgramRepair.bounded_repair]
  exact hcorrect input certificate

/-- The exact bound input counts both bit lists, including all extra source
input and certificate bits. It does not yet bound time solely by prefix length. -/
theorem pair_encoded_length (input certificate : List Bool) :
    (BitstringEncoding.bitEncode (input,certificate)).length =
      6*input.length+1+3*certificate.length :=
  Shared.ComplexityBridge.bitstring_pair_encoded_length input certificate

/-- One fixed source numeral executes the parsed checker at every later
clock on an already packed pair. The polynomial charges the complete packed
pair and its input boundary; no unbounded source-certificate loader is hidden. -/
theorem source_machine_exists (p time : Polynomial Nat) (original : EncRows) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (input certificate : List Bool) (extra : Nat),
        Source284Relative.accepts (Source284CompileRecords.compile program)
          (value (BitstringEncoding.bitEncode (input,certificate))) 0
          (clock.eval (BitstringEncoding.bitEncode (input,certificate)).length+extra) =
            relation p time original (input,certificate) := by
  obtain ⟨program,clock,hvalid,hcorrect⟩ := finite_program p time original
  refine ⟨program,clock,hvalid,?_⟩
  intro input certificate extra
  have hc := BoundedHardness.bounded_mono program (BitstringEncoding.bitEncode (input,certificate))
    (clock.eval (BitstringEncoding.bitEncode (input,certificate)).length)
    (clock.eval (BitstringEncoding.bitEncode (input,certificate)).length+extra)
    (relation p time original (input,certificate)) (by omega) (hcorrect input certificate)
  apply Bool.eq_iff_iff.mpr
  rw [Source284FiniteProgramRun.bounded_acceptance_shared program _ _ hvalid, hc]
  simp

/-- The same fixed source machine respects the original witness bound on
positive inputs whenever the supplied original verifier is valid and
computes the predicate for every alias. -/
theorem source_machine_positive (p time : Polynomial Nat) (original : EncRows)
    (hn : 0 < original.length) (hv : Source284ListTables.valid (decodeRows original) = true) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (input certificate : List Bool) (extra : Nat) (predicate : List Bool → Bool),
        0 < Source284Parser.length (value input) →
        (∀ c w, Source284TaggedWitnessCodec.decode
            (p.eval (2*Source284Parser.length (value input)+1)) c = some w →
          (Source284TableRun.run (Source284ListTables.table (decodeRows original))
            ⟨c,value input,some 0⟩ (time.eval (Source284Parser.length (value input))+1)).state.isNone =
              predicate w) →
        Source284Relative.accepts (Source284CompileRecords.compile program)
          (value (BitstringEncoding.bitEncode (input,certificate))) 0
          (clock.eval (BitstringEncoding.bitEncode (input,certificate)).length+extra) =
            Source284TaggedWitnessCodec.check (p.eval (2*Source284Parser.length (value input)+1))
              predicate (value certificate) := by
  obtain ⟨program,clock,hvalid,h⟩ := source_machine_exists p time original
  refine ⟨program,clock,hvalid,?_⟩
  intro input certificate extra predicate hi hmatch
  rw [h]
  exact Source284ParsedPolynomialGuard.check_positive p time (original,(input,certificate))
    predicate hi hn hv hmatch

end Shared.Beeping.NPcoNP.Source284PackedGuardCompiler
