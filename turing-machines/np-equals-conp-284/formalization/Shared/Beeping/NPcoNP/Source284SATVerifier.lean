import Shared.Beeping.NPcoNP.Source284CompileBitsTM2
import Shared.ComplexityBridge.FiniteVerifierCompiler
import Shared.ComplexityBridge.TM2PreparedVerify

/-! A fixed, valid finite verifier for the actual all-bitstrings SAT language,
with the original witness length bound and a common polynomial clock. This is
only a source-table bounded-acceptance fact. It does not construct a reduction,
load witnesses, charge the compiler or establish a literal-machine binding. -/
namespace Shared.Beeping.NPcoNP.Source284SATVerifier

open Shared.Codes.FinitePrograms
open Shared.Codes.TM2Candidate Shared.Codes.TM2CheckedCandidate
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation
open Shared.ComplexityBridge.TM2FiniteBoundary
open Shared.ComplexityBridge.FiniteVerifierCompiler
open Shared.ComplexityBridge.BoundedHardness
open Shared.Beeping.NPcoNP.Source284CompileBitsTM2
open Shared.Codes.BitNumeralCompare (value)

/-- Unlike the general compiler interface, retain the valid-table property
needed by the source-record compiler. -/
theorem valid_pair_verifier (R : (List Bool × List Bool) → Bool)
    (hR : ComplexityTheory.IsPolyTime R) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ x w, bounded program (BitstringEncoding.bitEncode (x,w))
        (clock.eval (BitstringEncoding.bitEncode (x,w)).length) = some (R (x,w)) := by
  obtain ⟨candidate,_,hcorrect⟩ := Shared.Codes.TM2PairCandidate.canonicalPoly_covers R hR
  obtain ⟨p,hdecode,hdata,hmain,hp,hout⟩ :=
    successful_parameters candidate (R ([],[])) (hcorrect [] [])
  have htotal : ∀ x w, ∃ b, Shared.Codes.TM2PairCandidate.evaluate candidate x w = some b := by
    intro x w
    exact ⟨R (x,w),hcorrect x w⟩
  obtain ⟨program,clock,hvalid,h⟩ :=
    Shared.Codes.FiniteProgramNumericPolynomial.compile_checked_if_total
      candidate p hdecode hdata hmain hp hout htotal
  refine ⟨program,clock,hvalid,?_⟩
  intro x w
  rw [h x w,hcorrect x w]

/-- One fixed finite source program recognizes SAT via a bounded list witness.
The input is the full canonical pair encoding, not a raw concatenation. The
source certificate is zero; loading the witness from the source's other tape
half, constructing the pair, and charging the outer reduction remain open. -/
theorem sat_fixed_source_verifier :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ x : List Bool,
        Shared.ComplexityBridge.CNF.sat x = true ↔
          ∃ w : List Bool, w.length ≤ x.length ∧
            Source284Relative.accepts (value (compileBits program))
              (value (BitstringEncoding.bitEncode (x,w))) 0
              (commonFuel Polynomial.X clock x) = true := by
  obtain ⟨program,clock,hvalid,hprogram⟩ :=
    valid_pair_verifier Shared.ComplexityBridge.CNFWitness.verify
      Shared.ComplexityBridge.TM2PreparedVerify.verify_isPolyTime
  refine ⟨program,clock,hvalid,?_⟩
  intro x
  rw [Shared.ComplexityBridge.CNFWitness.sat_iff_bounded_verifier]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  have hfuel := commonFuel_correct Shared.ComplexityBridge.CNFWitness.verify
    program Polynomial.X clock hprogram x w (by simpa using hw)
  rw [bounded_acceptance program hvalid, hfuel]
  simp

end Shared.Beeping.NPcoNP.Source284SATVerifier
